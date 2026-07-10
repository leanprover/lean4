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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___y_9072__boxed_647_; uint8_t v_suppressElabErrors_boxed_648_; uint8_t v_res_649_; lean_object* v_r_650_; 
v___y_9072__boxed_647_ = lean_unbox(v___y_644_);
v_suppressElabErrors_boxed_648_ = lean_unbox(v_suppressElabErrors_645_);
v_res_649_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___lam__0(v___y_9072__boxed_647_, v_suppressElabErrors_boxed_648_, v_x_646_);
lean_dec(v_x_646_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10(lean_object* v_ref_652_, lean_object* v_msgData_653_, uint8_t v_severity_654_, uint8_t v_isSilent_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___y_660_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; uint8_t v___y_723_; lean_object* v___y_724_; uint8_t v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; uint8_t v___y_751_; uint8_t v___y_752_; uint8_t v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; uint8_t v___y_759_; uint8_t v___y_760_; uint8_t v___y_761_; uint8_t v___x_776_; uint8_t v___y_778_; uint8_t v___y_779_; uint8_t v___y_780_; uint8_t v___y_782_; uint8_t v___x_794_; 
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
lean_ctor_set(v___x_693_, 1, v___y_663_);
lean_inc_ref(v___y_660_);
lean_inc_ref(v___y_664_);
v___x_694_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_694_, 0, v___y_664_);
lean_ctor_set(v___x_694_, 1, v___y_661_);
lean_ctor_set(v___x_694_, 2, v___y_665_);
lean_ctor_set(v___x_694_, 3, v___y_660_);
lean_ctor_set(v___x_694_, 4, v___x_693_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*5, v___y_666_);
lean_ctor_set_uint8(v___x_694_, sizeof(void*)*5 + 1, v___y_662_);
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
lean_dec(v___y_665_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_661_);
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
lean_dec(v___y_665_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v___y_661_);
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
v___x_737_ = l_Lean_FileMap_toPosition(v_fileMap_729_, v___y_724_);
lean_dec(v___y_724_);
v___x_738_ = l_Lean_FileMap_toPosition(v_fileMap_729_, v___y_727_);
lean_dec(v___y_727_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
if (v_suppressElabErrors_730_ == 0)
{
lean_del_object(v___x_735_);
v___y_660_ = v___x_740_;
v___y_661_ = v___x_737_;
v___y_662_ = v___y_725_;
v___y_663_ = v_a_733_;
v___y_664_ = v_fileName_728_;
v___y_665_ = v___x_739_;
v___y_666_ = v___y_726_;
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
v___y_660_ = v___x_740_;
v___y_661_ = v___x_737_;
v___y_662_ = v___y_725_;
v___y_663_ = v_a_733_;
v___y_664_ = v_fileName_728_;
v___y_665_ = v___x_739_;
v___y_666_ = v___y_726_;
v___y_667_ = v___y_657_;
goto v___jp_659_;
}
}
}
}
v___jp_750_:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Syntax_getTailPos_x3f(v___y_754_, v___y_753_);
lean_dec(v___y_754_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_inc(v___y_755_);
v___y_723_ = v___y_751_;
v___y_724_ = v___y_755_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_753_;
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
v___y_724_ = v___y_755_;
v___y_725_ = v___y_752_;
v___y_726_ = v___y_753_;
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
v___y_752_ = v___y_761_;
v___y_753_ = v___y_760_;
v___y_754_ = v_ref_764_;
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
v___y_752_ = v___y_761_;
v___y_753_ = v___y_760_;
v___y_754_ = v_ref_764_;
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
lean_object* v_env_1061_; lean_object* v_scopes_1062_; lean_object* v_usedQuotCtxts_1063_; lean_object* v_nextMacroScope_1064_; lean_object* v_maxRecDepth_1065_; lean_object* v_ngen_1066_; lean_object* v_auxDeclNGen_1067_; lean_object* v_infoState_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1145_; 
v_env_1061_ = lean_ctor_get(v_cmdState_1055_, 0);
v_scopes_1062_ = lean_ctor_get(v_cmdState_1055_, 2);
v_usedQuotCtxts_1063_ = lean_ctor_get(v_cmdState_1055_, 3);
v_nextMacroScope_1064_ = lean_ctor_get(v_cmdState_1055_, 4);
v_maxRecDepth_1065_ = lean_ctor_get(v_cmdState_1055_, 5);
v_ngen_1066_ = lean_ctor_get(v_cmdState_1055_, 6);
v_auxDeclNGen_1067_ = lean_ctor_get(v_cmdState_1055_, 7);
v_infoState_1068_ = lean_ctor_get(v_cmdState_1055_, 8);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_cmdState_1055_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; lean_object* v_unused_1147_; lean_object* v_unused_1148_; 
v_unused_1146_ = lean_ctor_get(v_cmdState_1055_, 10);
lean_dec(v_unused_1146_);
v_unused_1147_ = lean_ctor_get(v_cmdState_1055_, 9);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_cmdState_1055_, 1);
lean_dec(v_unused_1148_);
v___x_1070_ = v_cmdState_1055_;
v_isShared_1071_ = v_isSharedCheck_1145_;
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
v_isShared_1071_ = v_isSharedCheck_1145_;
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
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_env_1061_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_scopes_1062_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_usedQuotCtxts_1063_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_nextMacroScope_1064_);
lean_ctor_set(v_reuseFailAlloc_1144_, 5, v_maxRecDepth_1065_);
lean_ctor_set(v_reuseFailAlloc_1144_, 6, v_ngen_1066_);
lean_ctor_set(v_reuseFailAlloc_1144_, 7, v_auxDeclNGen_1067_);
lean_ctor_set(v_reuseFailAlloc_1144_, 8, v_infoState_1068_);
lean_ctor_set(v_reuseFailAlloc_1144_, 9, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1144_, 10, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
lean_object* v___x_1080_; lean_object* v_toProcessingContext_1081_; lean_object* v_fileName_1082_; lean_object* v_fileMap_1083_; lean_object* v_opts_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; uint8_t v___y_1094_; lean_object* v___y_1095_; lean_object* v_messages_1096_; lean_object* v___y_1122_; 
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
lean_object* v___x_1143_; 
lean_inc_ref(v_snap_1057_);
v___x_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_snap_1057_);
v___y_1122_ = v___x_1143_;
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
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*4, v___y_1094_);
v___x_1101_ = l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4(v___x_1086_, v___x_1100_);
v___x_1102_ = lean_io_promise_resolve(v___x_1101_, v_new_1097_);
lean_dec(v_new_1097_);
v_env_1103_ = lean_ctor_get(v___y_1095_, 0);
v_scopes_1104_ = lean_ctor_get(v___y_1095_, 2);
v_usedQuotCtxts_1105_ = lean_ctor_get(v___y_1095_, 3);
v_nextMacroScope_1106_ = lean_ctor_get(v___y_1095_, 4);
v_maxRecDepth_1107_ = lean_ctor_get(v___y_1095_, 5);
v_ngen_1108_ = lean_ctor_get(v___y_1095_, 6);
v_auxDeclNGen_1109_ = lean_ctor_get(v___y_1095_, 7);
v_infoState_1110_ = lean_ctor_get(v___y_1095_, 8);
v_traceState_1111_ = lean_ctor_get(v___y_1095_, 9);
v_snapshotTasks_1112_ = lean_ctor_get(v___y_1095_, 10);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___y_1095_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v___y_1095_, 1);
lean_dec(v_unused_1120_);
v___x_1114_ = v___y_1095_;
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
lean_dec(v___y_1095_);
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
lean_object* v___x_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v_fst_1130_; lean_object* v___x_1131_; lean_object* v_messages_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; uint8_t v___x_1135_; 
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
v___x_1135_ = lean_bool_not(v___x_1134_);
if (v___x_1135_ == 0)
{
lean_dec(v_fst_1130_);
lean_dec(v_beginPos_1056_);
v___y_1094_ = v___x_1124_;
v___y_1095_ = v___x_1131_;
v_messages_1096_ = v_messages_1132_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v_fileMap_1083_);
v___x_1136_ = l_Lean_FileMap_toPosition(v_fileMap_1083_, v_beginPos_1056_);
lean_dec(v_beginPos_1056_);
v___x_1137_ = 0;
v___x_1138_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_fst_1130_);
v___x_1140_ = l_Lean_MessageData_ofFormat(v___x_1139_);
lean_inc_ref(v_fileName_1082_);
v___x_1141_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1141_, 0, v_fileName_1082_);
lean_ctor_set(v___x_1141_, 1, v___x_1136_);
lean_ctor_set(v___x_1141_, 2, v___x_1088_);
lean_ctor_set(v___x_1141_, 3, v___x_1138_);
lean_ctor_set(v___x_1141_, 4, v___x_1140_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*5, v___x_1124_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*5 + 1, v___x_1137_);
lean_ctor_set_uint8(v___x_1141_, sizeof(void*)*5 + 2, v___x_1124_);
v___x_1142_ = l_Lean_MessageLog_add(v___x_1141_, v_messages_1132_);
v___y_1094_ = v___x_1124_;
v___y_1095_ = v___x_1131_;
v_messages_1096_ = v___x_1142_;
goto v___jp_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___boxed(lean_object* v_stx_1149_, lean_object* v_cmds_1150_, lean_object* v_cmdState_1151_, lean_object* v_beginPos_1152_, lean_object* v_snap_1153_, lean_object* v_cancelTk_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_stx_1149_, v_cmds_1150_, v_cmdState_1151_, v_beginPos_1152_, v_snap_1153_, v_cancelTk_1154_, v_a_1155_);
lean_dec_ref(v_a_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(lean_object* v_00_u03b1_1158_, lean_object* v_h_1159_, lean_object* v_x_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___redArg(v_h_1159_, v_x_1160_, v___y_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_h_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_IO_withStdin___at___00IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3_spec__5(v_00_u03b1_1164_, v_h_1165_, v_x_1166_, v___y_1167_);
lean_dec_ref(v___y_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(lean_object* v_00_u03b1_1170_, lean_object* v_x_1171_, uint8_t v_isolateStderr_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___redArg(v_x_1171_, v_isolateStderr_1172_, v___y_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_x_1177_, lean_object* v_isolateStderr_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_isolateStderr_boxed_1181_; lean_object* v_res_1182_; 
v_isolateStderr_boxed_1181_ = lean_unbox(v_isolateStderr_1178_);
v_res_1182_ = l_IO_FS_withIsolatedStreams___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__3(v_00_u03b1_1176_, v_x_1177_, v_isolateStderr_boxed_1181_, v___y_1179_);
lean_dec_ref(v___y_1179_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(lean_object* v_msgData_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___redArg(v_msgData_1183_, v___y_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11___boxed(lean_object* v_msgData_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10_spec__11(v_msgData_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__0(lean_object* v_a_1193_){
_start:
{
lean_object* v_toSnapshotTreeM_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_toSnapshotTreeM_1194_ = lean_ctor_get(v_a_1193_, 1);
lean_inc_ref(v_toSnapshotTreeM_1194_);
lean_dec_ref(v_a_1193_);
v___x_1195_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1196_ = lean_apply_1(v_toSnapshotTreeM_1194_, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__1(lean_object* v_a_1197_){
_start:
{
lean_object* v_toSnapshot_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1208_; 
v_toSnapshot_1198_ = lean_ctor_get(v_a_1197_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v_a_1197_, 1);
lean_dec(v_unused_1209_);
v___x_1200_ = v_a_1197_;
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_toSnapshot_1198_);
lean_dec(v_a_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1202_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1203_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_1198_, v___x_1202_);
v___x_1204_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1204_);
lean_ctor_set(v___x_1200_, 0, v___x_1203_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__2(lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1212_ = l_Lean_Language_Snapshot_transform(v_a_1210_, v___x_1211_);
v___x_1213_ = ((lean_object*)(l_Lean_Language_DynamicSnapshot_ofTyped___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__4___lam__0___closed__0));
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(lean_object* v_opts_1215_, lean_object* v_opt_1216_){
_start:
{
lean_object* v_name_1217_; lean_object* v_defValue_1218_; lean_object* v_map_1219_; lean_object* v___x_1220_; 
v_name_1217_ = lean_ctor_get(v_opt_1216_, 0);
v_defValue_1218_ = lean_ctor_get(v_opt_1216_, 1);
v_map_1219_ = lean_ctor_get(v_opts_1215_, 0);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1219_, v_name_1217_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_inc(v_defValue_1218_);
return v_defValue_1218_;
}
else
{
lean_object* v_val_1221_; 
v_val_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1221_);
lean_dec_ref_known(v___x_1220_, 1);
if (lean_obj_tag(v_val_1221_) == 3)
{
lean_object* v_v_1222_; 
v_v_1222_ = lean_ctor_get(v_val_1221_, 0);
lean_inc(v_v_1222_);
lean_dec_ref_known(v_val_1221_, 1);
return v_v_1222_;
}
else
{
lean_dec(v_val_1221_);
lean_inc(v_defValue_1218_);
return v_defValue_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3___boxed(lean_object* v_opts_1223_, lean_object* v_opt_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1223_, v_opt_1224_);
lean_dec_ref(v_opt_1224_);
lean_dec_ref(v_opts_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__5(lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_1228_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_1226_, v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1235_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1236_ = l_Lean_Name_append(v___x_1235_, v___x_1234_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(lean_object* v___x_1237_, lean_object* v___x_1238_, uint8_t v_val_1239_, lean_object* v_val_1240_, lean_object* v_val_1241_, lean_object* v___x_1242_, lean_object* v___x_1243_, uint8_t v___x_1244_, lean_object* v_a_1245_, lean_object* v_pos_1246_, lean_object* v_infoSt_1247_){
_start:
{
lean_object* v___y_1250_; lean_object* v_msgLog_1251_; lean_object* v___y_1257_; lean_object* v_trees_1289_; lean_object* v_size_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_trees_1289_ = lean_ctor_get(v_infoSt_1247_, 2);
v_size_1290_ = lean_ctor_get(v_trees_1289_, 2);
v___x_1291_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_1292_ = lean_nat_dec_lt(v___x_1243_, v_size_1290_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = l_outOfBounds___redArg(v___x_1291_);
v___y_1257_ = v___x_1293_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1291_, v_trees_1289_, v___x_1243_);
v___y_1257_ = v___x_1294_;
goto v___jp_1256_;
}
v___jp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_msgLog_1251_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___y_1250_);
v___x_1254_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1254_, 0, v___x_1237_);
lean_ctor_set(v___x_1254_, 1, v___x_1252_);
lean_ctor_set(v___x_1254_, 2, v___x_1253_);
lean_ctor_set(v___x_1254_, 3, v___x_1238_);
lean_ctor_set_uint8(v___x_1254_, sizeof(void*)*4, v_val_1239_);
v___x_1255_ = lean_io_promise_resolve(v___x_1254_, v_val_1240_);
return v___x_1255_;
}
v___jp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v_scopes_1260_; lean_object* v___x_1261_; lean_object* v_opts_1262_; uint8_t v_hasTrace_1263_; lean_object* v___x_1264_; 
v___x_1258_ = l_Lean_inheritedTraceOptions;
v___x_1259_ = lean_st_ref_get(v___x_1258_);
v_scopes_1260_ = lean_ctor_get(v_val_1241_, 2);
v___x_1261_ = l_List_head_x21___redArg(v___x_1242_, v_scopes_1260_);
v_opts_1262_ = lean_ctor_get(v___x_1261_, 1);
lean_inc_ref(v_opts_1262_);
lean_dec(v___x_1261_);
v_hasTrace_1263_ = lean_ctor_get_uint8(v_opts_1262_, sizeof(void*)*1);
v___x_1264_ = l_Lean_MessageLog_empty;
if (v_hasTrace_1263_ == 0)
{
lean_dec_ref(v_opts_1262_);
lean_dec(v___x_1259_);
lean_dec(v___x_1243_);
v___y_1250_ = v___y_1257_;
v_msgLog_1251_ = v___x_1264_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__2));
v___x_1266_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Language_Lean_setOption_spec__0___closed__1));
v___x_1267_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___closed__3);
v___x_1268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_1259_, v_opts_1262_, v___x_1267_);
lean_dec_ref(v_opts_1262_);
lean_dec(v___x_1259_);
if (v___x_1268_ == 0)
{
lean_dec(v___x_1243_);
v___y_1250_ = v___y_1257_;
v_msgLog_1251_ = v___x_1264_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_box(0);
lean_inc_ref(v___y_1257_);
v___x_1270_ = l_Lean_Elab_InfoTree_format(v___y_1257_, v___x_1269_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; double v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_toProcessingContext_1275_; lean_object* v_fileName_1276_; lean_object* v_fileMap_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1270_, 1);
v___x_1272_ = lean_float_of_nat(v___x_1243_);
v___x_1273_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_1274_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1274_, 0, v___x_1265_);
lean_ctor_set(v___x_1274_, 1, v___x_1269_);
lean_ctor_set(v___x_1274_, 2, v___x_1273_);
lean_ctor_set_float(v___x_1274_, sizeof(void*)*3, v___x_1272_);
lean_ctor_set_float(v___x_1274_, sizeof(void*)*3 + 8, v___x_1272_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*3 + 16, v___x_1244_);
v_toProcessingContext_1275_ = lean_ctor_get(v_a_1245_, 0);
v_fileName_1276_ = lean_ctor_get(v_toProcessingContext_1275_, 1);
v_fileMap_1277_ = lean_ctor_get(v_toProcessingContext_1275_, 2);
v___x_1278_ = l_Lean_MessageData_nil;
v___x_1279_ = l_Lean_MessageData_ofFormat(v_a_1271_);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_mk_empty_array_with_capacity(v___x_1280_);
v___x_1282_ = lean_array_push(v___x_1281_, v___x_1279_);
v___x_1283_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1274_);
lean_ctor_set(v___x_1283_, 1, v___x_1278_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1266_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
lean_inc_ref(v_fileMap_1277_);
v___x_1285_ = l_Lean_FileMap_toPosition(v_fileMap_1277_, v_pos_1246_);
v___x_1286_ = 0;
lean_inc_ref(v_fileName_1276_);
v___x_1287_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1287_, 0, v_fileName_1276_);
lean_ctor_set(v___x_1287_, 1, v___x_1285_);
lean_ctor_set(v___x_1287_, 2, v___x_1269_);
lean_ctor_set(v___x_1287_, 3, v___x_1273_);
lean_ctor_set(v___x_1287_, 4, v___x_1284_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*5, v_val_1239_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*5 + 1, v___x_1286_);
lean_ctor_set_uint8(v___x_1287_, sizeof(void*)*5 + 2, v_val_1239_);
v___x_1288_ = l_Lean_MessageLog_add(v___x_1287_, v___x_1264_);
v___y_1250_ = v___y_1257_;
v_msgLog_1251_ = v___x_1288_;
goto v___jp_1249_;
}
else
{
lean_dec_ref_known(v___x_1270_, 1);
lean_dec(v___x_1243_);
v___y_1250_ = v___y_1257_;
v_msgLog_1251_ = v___x_1264_;
goto v___jp_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed(lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_val_1297_, lean_object* v_val_1298_, lean_object* v_val_1299_, lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v_a_1303_, lean_object* v_pos_1304_, lean_object* v_infoSt_1305_, lean_object* v___y_1306_){
_start:
{
uint8_t v_val_44422__boxed_1307_; uint8_t v___x_44427__boxed_1308_; lean_object* v_res_1309_; 
v_val_44422__boxed_1307_ = lean_unbox(v_val_1297_);
v___x_44427__boxed_1308_ = lean_unbox(v___x_1302_);
v_res_1309_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4(v___x_1295_, v___x_1296_, v_val_44422__boxed_1307_, v_val_1298_, v_val_1299_, v___x_1300_, v___x_1301_, v___x_44427__boxed_1308_, v_a_1303_, v_pos_1304_, v_infoSt_1305_);
lean_dec_ref(v_infoSt_1305_);
lean_dec(v_pos_1304_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_val_1299_);
lean_dec(v_val_1298_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, uint8_t v_val_1313_, lean_object* v_as_1314_, size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_b_1317_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___x_1310_);
return v_b_1317_;
}
else
{
lean_object* v_snd_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1338_; 
v_snd_1320_ = lean_ctor_get(v_b_1317_, 1);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_b_1317_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_b_1317_, 0);
lean_dec(v_unused_1339_);
v___x_1322_ = v_b_1317_;
v_isShared_1323_ = v_isSharedCheck_1338_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1320_);
lean_dec(v_b_1317_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1338_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_a_1324_; lean_object* v_msg_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v_a_1324_ = lean_array_uget_borrowed(v_as_1314_, v_i_1316_);
v_msg_1325_ = lean_ctor_get(v_a_1324_, 1);
v___x_1326_ = lean_box(0);
lean_inc_ref(v___x_1310_);
v___x_1327_ = l_Lean_FileMap_toPosition(v___x_1310_, v___x_1311_);
v___x_1328_ = 0;
v___x_1329_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1325_);
lean_inc_ref(v___x_1312_);
v___x_1330_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1330_, 0, v___x_1312_);
lean_ctor_set(v___x_1330_, 1, v___x_1327_);
lean_ctor_set(v___x_1330_, 2, v___x_1326_);
lean_ctor_set(v___x_1330_, 3, v___x_1329_);
lean_ctor_set(v___x_1330_, 4, v_msg_1325_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*5, v_val_1313_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*5 + 1, v___x_1328_);
lean_ctor_set_uint8(v___x_1330_, sizeof(void*)*5 + 2, v_val_1313_);
v___x_1331_ = l_Lean_MessageLog_add(v___x_1330_, v_snd_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1331_);
lean_ctor_set(v___x_1322_, 0, v___x_1326_);
v___x_1333_ = v___x_1322_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
size_t v___x_1334_; size_t v___x_1335_; 
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1316_, v___x_1334_);
v_i_1316_ = v___x_1335_;
v_b_1317_ = v___x_1333_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9___boxed(lean_object* v___x_1340_, lean_object* v___x_1341_, lean_object* v___x_1342_, lean_object* v_val_1343_, lean_object* v_as_1344_, lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_b_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_val_44534__boxed_1349_; size_t v_sz_boxed_1350_; size_t v_i_boxed_1351_; lean_object* v_res_1352_; 
v_val_44534__boxed_1349_ = lean_unbox(v_val_1343_);
v_sz_boxed_1350_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1351_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1340_, v___x_1341_, v___x_1342_, v_val_44534__boxed_1349_, v_as_1344_, v_sz_boxed_1350_, v_i_boxed_1351_, v_b_1347_);
lean_dec_ref(v_as_1344_);
lean_dec(v___x_1341_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(lean_object* v___x_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, uint8_t v_val_1356_, lean_object* v_as_1357_, size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_b_1360_){
_start:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_usize_dec_lt(v_i_1359_, v_sz_1358_);
if (v___x_1362_ == 0)
{
lean_dec_ref(v___x_1355_);
lean_dec_ref(v___x_1353_);
return v_b_1360_;
}
else
{
lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1381_; 
v_snd_1363_ = lean_ctor_get(v_b_1360_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_b_1360_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_b_1360_, 0);
lean_dec(v_unused_1382_);
v___x_1365_ = v_b_1360_;
v_isShared_1366_ = v_isSharedCheck_1381_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_dec(v_b_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1381_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_a_1367_; lean_object* v_msg_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v_a_1367_ = lean_array_uget_borrowed(v_as_1357_, v_i_1359_);
v_msg_1368_ = lean_ctor_get(v_a_1367_, 1);
v___x_1369_ = lean_box(0);
lean_inc_ref(v___x_1353_);
v___x_1370_ = l_Lean_FileMap_toPosition(v___x_1353_, v___x_1354_);
v___x_1371_ = 0;
v___x_1372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1368_);
lean_inc_ref(v___x_1355_);
v___x_1373_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1373_, 0, v___x_1355_);
lean_ctor_set(v___x_1373_, 1, v___x_1370_);
lean_ctor_set(v___x_1373_, 2, v___x_1369_);
lean_ctor_set(v___x_1373_, 3, v___x_1372_);
lean_ctor_set(v___x_1373_, 4, v_msg_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*5, v_val_1356_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*5 + 1, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*5 + 2, v_val_1356_);
v___x_1374_ = l_Lean_MessageLog_add(v___x_1373_, v_snd_1363_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1374_);
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1376_ = v___x_1365_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = ((size_t)1ULL);
v___x_1378_ = lean_usize_add(v_i_1359_, v___x_1377_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7_spec__9(v___x_1353_, v___x_1354_, v___x_1355_, v_val_1356_, v_as_1357_, v_sz_1358_, v___x_1378_, v___x_1376_);
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7___boxed(lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v___x_1385_, lean_object* v_val_1386_, lean_object* v_as_1387_, lean_object* v_sz_1388_, lean_object* v_i_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_val_44586__boxed_1392_; size_t v_sz_boxed_1393_; size_t v_i_boxed_1394_; lean_object* v_res_1395_; 
v_val_44586__boxed_1392_ = lean_unbox(v_val_1386_);
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1388_);
lean_dec(v_sz_1388_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1383_, v___x_1384_, v___x_1385_, v_val_44586__boxed_1392_, v_as_1387_, v_sz_boxed_1393_, v_i_boxed_1394_, v_b_1390_);
lean_dec_ref(v_as_1387_);
lean_dec(v___x_1384_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(lean_object* v_init_1396_, lean_object* v___x_1397_, lean_object* v___x_1398_, lean_object* v___x_1399_, uint8_t v_val_1400_, lean_object* v_n_1401_, lean_object* v_b_1402_){
_start:
{
if (lean_obj_tag(v_n_1401_) == 0)
{
lean_object* v_cs_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; size_t v_sz_1407_; size_t v___x_1408_; lean_object* v___x_1409_; lean_object* v_fst_1410_; 
v_cs_1404_ = lean_ctor_get(v_n_1401_, 0);
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v_b_1402_);
v_sz_1407_ = lean_array_size(v_cs_1404_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1396_, v___x_1397_, v___x_1398_, v___x_1399_, v_val_1400_, v_cs_1404_, v_sz_1407_, v___x_1408_, v___x_1406_);
v_fst_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_fst_1410_);
if (lean_obj_tag(v_fst_1410_) == 0)
{
lean_object* v_snd_1411_; lean_object* v___x_1412_; 
v_snd_1411_ = lean_ctor_get(v___x_1409_, 1);
lean_inc(v_snd_1411_);
lean_dec_ref(v___x_1409_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_snd_1411_);
return v___x_1412_;
}
else
{
lean_object* v_val_1413_; 
lean_dec_ref(v___x_1409_);
v_val_1413_ = lean_ctor_get(v_fst_1410_, 0);
lean_inc(v_val_1413_);
lean_dec_ref_known(v_fst_1410_, 1);
return v_val_1413_;
}
}
else
{
lean_object* v_vs_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; size_t v_sz_1417_; size_t v___x_1418_; lean_object* v___x_1419_; lean_object* v_fst_1420_; 
v_vs_1414_ = lean_ctor_get(v_n_1401_, 0);
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
lean_ctor_set(v___x_1416_, 1, v_b_1402_);
v_sz_1417_ = lean_array_size(v_vs_1414_);
v___x_1418_ = ((size_t)0ULL);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__7(v___x_1397_, v___x_1398_, v___x_1399_, v_val_1400_, v_vs_1414_, v_sz_1417_, v___x_1418_, v___x_1416_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(lean_object* v_init_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v___x_1427_, uint8_t v_val_1428_, lean_object* v_as_1429_, size_t v_sz_1430_, size_t v_i_1431_, lean_object* v_b_1432_){
_start:
{
uint8_t v___x_1434_; 
v___x_1434_ = lean_usize_dec_lt(v_i_1431_, v_sz_1430_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v___x_1427_);
lean_dec_ref(v___x_1425_);
return v_b_1432_;
}
else
{
lean_object* v_snd_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1453_; 
v_snd_1435_ = lean_ctor_get(v_b_1432_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_b_1432_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_b_1432_, 0);
lean_dec(v_unused_1454_);
v___x_1437_ = v_b_1432_;
v_isShared_1438_ = v_isSharedCheck_1453_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snd_1435_);
lean_dec(v_b_1432_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1453_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_a_1439_; lean_object* v___x_1440_; 
v_a_1439_ = lean_array_uget_borrowed(v_as_1429_, v_i_1431_);
lean_inc(v_snd_1435_);
lean_inc_ref(v___x_1427_);
lean_inc_ref(v___x_1425_);
v___x_1440_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1424_, v___x_1425_, v___x_1426_, v___x_1427_, v_val_1428_, v_a_1439_, v_snd_1435_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
lean_dec_ref(v___x_1427_);
lean_dec_ref(v___x_1425_);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1441_);
v___x_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_snd_1435_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
lean_dec(v_snd_1435_);
v_a_1445_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1445_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1446_ = lean_box(0);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v_a_1445_);
lean_ctor_set(v___x_1437_, 0, v___x_1446_);
v___x_1448_ = v___x_1437_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_a_1445_);
v___x_1448_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
size_t v___x_1449_; size_t v___x_1450_; 
v___x_1449_ = ((size_t)1ULL);
v___x_1450_ = lean_usize_add(v_i_1431_, v___x_1449_);
v_i_1431_ = v___x_1450_;
v_b_1432_ = v___x_1448_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6___boxed(lean_object* v_init_1455_, lean_object* v___x_1456_, lean_object* v___x_1457_, lean_object* v___x_1458_, lean_object* v_val_1459_, lean_object* v_as_1460_, lean_object* v_sz_1461_, lean_object* v_i_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_){
_start:
{
uint8_t v_val_44637__boxed_1465_; size_t v_sz_boxed_1466_; size_t v_i_boxed_1467_; lean_object* v_res_1468_; 
v_val_44637__boxed_1465_ = lean_unbox(v_val_1459_);
v_sz_boxed_1466_ = lean_unbox_usize(v_sz_1461_);
lean_dec(v_sz_1461_);
v_i_boxed_1467_ = lean_unbox_usize(v_i_1462_);
lean_dec(v_i_1462_);
v_res_1468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4_spec__6(v_init_1455_, v___x_1456_, v___x_1457_, v___x_1458_, v_val_44637__boxed_1465_, v_as_1460_, v_sz_boxed_1466_, v_i_boxed_1467_, v_b_1463_);
lean_dec_ref(v_as_1460_);
lean_dec(v___x_1457_);
lean_dec_ref(v_init_1455_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4___boxed(lean_object* v_init_1469_, lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v_val_1473_, lean_object* v_n_1474_, lean_object* v_b_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v_val_44653__boxed_1477_; lean_object* v_res_1478_; 
v_val_44653__boxed_1477_ = lean_unbox(v_val_1473_);
v_res_1478_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1469_, v___x_1470_, v___x_1471_, v___x_1472_, v_val_44653__boxed_1477_, v_n_1474_, v_b_1475_);
lean_dec_ref(v_n_1474_);
lean_dec(v___x_1471_);
lean_dec_ref(v_init_1469_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, uint8_t v_val_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1488_ == 0)
{
lean_dec_ref(v___x_1481_);
lean_dec_ref(v___x_1479_);
return v_b_1486_;
}
else
{
lean_object* v_snd_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1507_; 
v_snd_1489_ = lean_ctor_get(v_b_1486_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_b_1486_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_b_1486_, 0);
lean_dec(v_unused_1508_);
v___x_1491_ = v_b_1486_;
v_isShared_1492_ = v_isSharedCheck_1507_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snd_1489_);
lean_dec(v_b_1486_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1507_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_a_1493_; lean_object* v_msg_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v_a_1493_ = lean_array_uget_borrowed(v_as_1483_, v_i_1485_);
v_msg_1494_ = lean_ctor_get(v_a_1493_, 1);
v___x_1495_ = lean_box(0);
lean_inc_ref(v___x_1479_);
v___x_1496_ = l_Lean_FileMap_toPosition(v___x_1479_, v___x_1480_);
v___x_1497_ = 0;
v___x_1498_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1494_);
lean_inc_ref(v___x_1481_);
v___x_1499_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1499_, 0, v___x_1481_);
lean_ctor_set(v___x_1499_, 1, v___x_1496_);
lean_ctor_set(v___x_1499_, 2, v___x_1495_);
lean_ctor_set(v___x_1499_, 3, v___x_1498_);
lean_ctor_set(v___x_1499_, 4, v_msg_1494_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*5, v_val_1482_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*5 + 1, v___x_1497_);
lean_ctor_set_uint8(v___x_1499_, sizeof(void*)*5 + 2, v_val_1482_);
v___x_1500_ = l_Lean_MessageLog_add(v___x_1499_, v_snd_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1500_);
lean_ctor_set(v___x_1491_, 0, v___x_1495_);
v___x_1502_ = v___x_1491_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
size_t v___x_1503_; size_t v___x_1504_; 
v___x_1503_ = ((size_t)1ULL);
v___x_1504_ = lean_usize_add(v_i_1485_, v___x_1503_);
v_i_1485_ = v___x_1504_;
v_b_1486_ = v___x_1502_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9___boxed(lean_object* v___x_1509_, lean_object* v___x_1510_, lean_object* v___x_1511_, lean_object* v_val_1512_, lean_object* v_as_1513_, lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_b_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v_val_44735__boxed_1518_; size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_val_44735__boxed_1518_ = lean_unbox(v_val_1512_);
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1509_, v___x_1510_, v___x_1511_, v_val_44735__boxed_1518_, v_as_1513_, v_sz_boxed_1519_, v_i_boxed_1520_, v_b_1516_);
lean_dec_ref(v_as_1513_);
lean_dec(v___x_1510_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(lean_object* v___x_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, uint8_t v_val_1525_, lean_object* v_as_1526_, size_t v_sz_1527_, size_t v_i_1528_, lean_object* v_b_1529_){
_start:
{
uint8_t v___x_1531_; 
v___x_1531_ = lean_usize_dec_lt(v_i_1528_, v_sz_1527_);
if (v___x_1531_ == 0)
{
lean_dec_ref(v___x_1524_);
lean_dec_ref(v___x_1522_);
return v_b_1529_;
}
else
{
lean_object* v_snd_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1550_; 
v_snd_1532_ = lean_ctor_get(v_b_1529_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_b_1529_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_b_1529_, 0);
lean_dec(v_unused_1551_);
v___x_1534_ = v_b_1529_;
v_isShared_1535_ = v_isSharedCheck_1550_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_snd_1532_);
lean_dec(v_b_1529_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1550_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_a_1536_; lean_object* v_msg_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v_a_1536_ = lean_array_uget_borrowed(v_as_1526_, v_i_1528_);
v_msg_1537_ = lean_ctor_get(v_a_1536_, 1);
v___x_1538_ = lean_box(0);
lean_inc_ref(v___x_1522_);
v___x_1539_ = l_Lean_FileMap_toPosition(v___x_1522_, v___x_1523_);
v___x_1540_ = 0;
v___x_1541_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
lean_inc_ref(v_msg_1537_);
lean_inc_ref(v___x_1524_);
v___x_1542_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1542_, 0, v___x_1524_);
lean_ctor_set(v___x_1542_, 1, v___x_1539_);
lean_ctor_set(v___x_1542_, 2, v___x_1538_);
lean_ctor_set(v___x_1542_, 3, v___x_1541_);
lean_ctor_set(v___x_1542_, 4, v_msg_1537_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*5, v_val_1525_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*5 + 1, v___x_1540_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*5 + 2, v_val_1525_);
v___x_1543_ = l_Lean_MessageLog_add(v___x_1542_, v_snd_1532_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v___x_1543_);
lean_ctor_set(v___x_1534_, 0, v___x_1538_);
v___x_1545_ = v___x_1534_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = ((size_t)1ULL);
v___x_1547_ = lean_usize_add(v_i_1528_, v___x_1546_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5_spec__9(v___x_1522_, v___x_1523_, v___x_1524_, v_val_1525_, v_as_1526_, v_sz_1527_, v___x_1547_, v___x_1545_);
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5___boxed(lean_object* v___x_1552_, lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v_val_1555_, lean_object* v_as_1556_, lean_object* v_sz_1557_, lean_object* v_i_1558_, lean_object* v_b_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v_val_44787__boxed_1561_; size_t v_sz_boxed_1562_; size_t v_i_boxed_1563_; lean_object* v_res_1564_; 
v_val_44787__boxed_1561_ = lean_unbox(v_val_1555_);
v_sz_boxed_1562_ = lean_unbox_usize(v_sz_1557_);
lean_dec(v_sz_1557_);
v_i_boxed_1563_ = lean_unbox_usize(v_i_1558_);
lean_dec(v_i_1558_);
v_res_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1552_, v___x_1553_, v___x_1554_, v_val_44787__boxed_1561_, v_as_1556_, v_sz_boxed_1562_, v_i_boxed_1563_, v_b_1559_);
lean_dec_ref(v_as_1556_);
lean_dec(v___x_1553_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(lean_object* v___x_1565_, lean_object* v___x_1566_, lean_object* v___x_1567_, uint8_t v_val_1568_, lean_object* v_t_1569_, lean_object* v_init_1570_){
_start:
{
lean_object* v_root_1572_; lean_object* v_tail_1573_; lean_object* v___x_1574_; 
v_root_1572_ = lean_ctor_get(v_t_1569_, 0);
v_tail_1573_ = lean_ctor_get(v_t_1569_, 1);
lean_inc_ref(v___x_1567_);
lean_inc_ref(v___x_1565_);
lean_inc_ref(v_init_1570_);
v___x_1574_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__4(v_init_1570_, v___x_1565_, v___x_1566_, v___x_1567_, v_val_1568_, v_root_1572_, v_init_1570_);
lean_dec_ref(v_init_1570_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; 
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1565_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
return v_a_1575_;
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; size_t v_sz_1579_; size_t v___x_1580_; lean_object* v___x_1581_; lean_object* v_fst_1582_; 
v_a_1576_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v_a_1576_);
v_sz_1579_ = lean_array_size(v_tail_1573_);
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4_spec__5(v___x_1565_, v___x_1566_, v___x_1567_, v_val_1568_, v_tail_1573_, v_sz_1579_, v___x_1580_, v___x_1578_);
v_fst_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_fst_1582_);
if (lean_obj_tag(v_fst_1582_) == 0)
{
lean_object* v_snd_1583_; 
v_snd_1583_ = lean_ctor_get(v___x_1581_, 1);
lean_inc(v_snd_1583_);
lean_dec_ref(v___x_1581_);
return v_snd_1583_;
}
else
{
lean_object* v_val_1584_; 
lean_dec_ref(v___x_1581_);
v_val_1584_ = lean_ctor_get(v_fst_1582_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v_fst_1582_, 1);
return v_val_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4___boxed(lean_object* v___x_1585_, lean_object* v___x_1586_, lean_object* v___x_1587_, lean_object* v_val_1588_, lean_object* v_t_1589_, lean_object* v_init_1590_, lean_object* v___y_1591_){
_start:
{
uint8_t v_val_44838__boxed_1592_; lean_object* v_res_1593_; 
v_val_44838__boxed_1592_ = lean_unbox(v_val_1588_);
v_res_1593_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v___x_1585_, v___x_1586_, v___x_1587_, v_val_44838__boxed_1592_, v_t_1589_, v_init_1590_);
lean_dec_ref(v_t_1589_);
lean_dec(v___x_1586_);
return v_res_1593_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_unsigned_to_nat(1u);
v___x_1595_ = l_Lean_firstFrontendMacroScope;
v___x_1596_ = lean_nat_add(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4(void){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1603_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__4);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, size_t v___x_1611_, uint8_t v___x_1612_, lean_object* v_env_1613_, lean_object* v___x_1614_, lean_object* v___x_1615_, lean_object* v_a_1616_, lean_object* v_opts_1617_, lean_object* v___x_1618_, lean_object* v_pos_1619_, uint8_t v_val_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v___x_1624_, uint8_t v___x_1625_, lean_object* v_x_1626_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v_toProcessingContext_1647_; lean_object* v_fileName_1648_; lean_object* v_fileMap_1649_; lean_object* v_env_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; lean_object* v_fileName_1656_; lean_object* v_fileMap_1657_; lean_object* v_currRecDepth_1658_; lean_object* v_ref_1659_; lean_object* v_currNamespace_1660_; lean_object* v_openDecls_1661_; lean_object* v_initHeartbeats_1662_; lean_object* v_maxHeartbeats_1663_; lean_object* v_quotContext_1664_; lean_object* v_currMacroScope_1665_; lean_object* v_cancelTk_x3f_1666_; uint8_t v_suppressElabErrors_1667_; lean_object* v_inheritedTraceOptions_1668_; lean_object* v___y_1669_; uint8_t v___y_1686_; uint8_t v___x_1707_; 
v___x_1628_ = l_Lean_firstFrontendMacroScope;
v___x_1629_ = lean_unsigned_to_nat(1u);
v___x_1630_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_1631_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_1632_ = lean_box(0);
lean_inc(v___x_1608_);
v___x_1633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1608_);
lean_ctor_set(v___x_1633_, 1, v___x_1629_);
lean_ctor_set(v___x_1633_, 2, v___x_1632_);
v___x_1634_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__5);
v___x_1635_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__6);
v___x_1636_ = lean_mk_empty_array_with_capacity(v___x_1609_);
lean_inc_ref(v___x_1636_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_inc_n(v___x_1610_, 2);
v___x_1638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1636_);
lean_ctor_set(v___x_1638_, 2, v___x_1610_);
lean_ctor_set(v___x_1638_, 3, v___x_1610_);
lean_ctor_set_usize(v___x_1638_, 4, v___x_1611_);
v___x_1639_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_1638_, 2);
v___x_1640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1638_);
lean_ctor_set(v___x_1640_, 2, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1641_, 0, v___x_1634_);
lean_ctor_set(v___x_1641_, 1, v___x_1634_);
lean_ctor_set(v___x_1641_, 2, v___x_1638_);
lean_ctor_set_uint8(v___x_1641_, sizeof(void*)*3, v___x_1612_);
v___x_1642_ = lean_mk_empty_array_with_capacity(v___x_1610_);
lean_inc_ref(v___x_1642_);
lean_inc_ref(v___x_1614_);
v___x_1643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1643_, 0, v_env_1613_);
lean_ctor_set(v___x_1643_, 1, v___x_1630_);
lean_ctor_set(v___x_1643_, 2, v___x_1631_);
lean_ctor_set(v___x_1643_, 3, v___x_1633_);
lean_ctor_set(v___x_1643_, 4, v___x_1614_);
lean_ctor_set(v___x_1643_, 5, v___x_1635_);
lean_ctor_set(v___x_1643_, 6, v___x_1640_);
lean_ctor_set(v___x_1643_, 7, v___x_1641_);
lean_ctor_set(v___x_1643_, 8, v___x_1642_);
v___x_1644_ = lean_st_mk_ref(v___x_1643_);
v___x_1645_ = lean_st_ref_get(v___x_1615_);
v___x_1646_ = lean_st_ref_get(v___x_1644_);
v_toProcessingContext_1647_ = lean_ctor_get(v_a_1616_, 0);
v_fileName_1648_ = lean_ctor_get(v_toProcessingContext_1647_, 1);
v_fileMap_1649_ = lean_ctor_get(v_toProcessingContext_1647_, 2);
v_env_1650_ = lean_ctor_get(v___x_1646_, 0);
lean_inc_ref(v_env_1650_);
lean_dec(v___x_1646_);
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Lean_Core_getMaxHeartbeats(v_opts_1617_);
v___x_1653_ = l_Lean_diagnostics;
v___x_1654_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1617_, v___x_1653_);
v___x_1707_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_1650_);
lean_dec_ref(v_env_1650_);
if (v___x_1707_ == 0)
{
if (v___x_1654_ == 0)
{
v___y_1686_ = v___x_1625_;
goto v___jp_1685_;
}
else
{
v___y_1686_ = v___x_1707_;
goto v___jp_1685_;
}
}
else
{
v___y_1686_ = v___x_1654_;
goto v___jp_1685_;
}
v___jp_1655_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1670_ = l_Lean_maxRecDepth;
v___x_1671_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__3(v_opts_1617_, v___x_1670_);
lean_inc(v_currMacroScope_1665_);
lean_inc(v_openDecls_1661_);
lean_inc(v_ref_1659_);
v___x_1672_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1672_, 0, v_fileName_1656_);
lean_ctor_set(v___x_1672_, 1, v_fileMap_1657_);
lean_ctor_set(v___x_1672_, 2, v_opts_1617_);
lean_ctor_set(v___x_1672_, 3, v_currRecDepth_1658_);
lean_ctor_set(v___x_1672_, 4, v___x_1671_);
lean_ctor_set(v___x_1672_, 5, v_ref_1659_);
lean_ctor_set(v___x_1672_, 6, v_currNamespace_1660_);
lean_ctor_set(v___x_1672_, 7, v_openDecls_1661_);
lean_ctor_set(v___x_1672_, 8, v_initHeartbeats_1662_);
lean_ctor_set(v___x_1672_, 9, v_maxHeartbeats_1663_);
lean_ctor_set(v___x_1672_, 10, v_quotContext_1664_);
lean_ctor_set(v___x_1672_, 11, v_currMacroScope_1665_);
lean_ctor_set(v___x_1672_, 12, v_cancelTk_x3f_1666_);
lean_ctor_set(v___x_1672_, 13, v_inheritedTraceOptions_1668_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*14, v___x_1654_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*14 + 1, v_suppressElabErrors_1667_);
v___x_1673_ = l_Lean_Language_SnapshotTree_trace(v___x_1618_, v___x_1672_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref_known(v___x_1672_, 14);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; lean_object* v_traceState_1675_; lean_object* v_traces_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec_ref_known(v___x_1673_, 1);
lean_dec_ref(v___x_1623_);
v___x_1674_ = lean_st_ref_get(v___x_1644_);
lean_dec(v___x_1644_);
v_traceState_1675_ = lean_ctor_get(v___x_1674_, 4);
lean_inc_ref(v_traceState_1675_);
lean_dec(v___x_1674_);
v_traces_1676_ = lean_ctor_get(v_traceState_1675_, 0);
lean_inc_ref(v_traces_1676_);
lean_dec_ref(v_traceState_1675_);
v___x_1677_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_fileName_1648_);
lean_inc_ref(v_fileMap_1649_);
v___x_1678_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__4(v_fileMap_1649_, v_pos_1619_, v_fileName_1648_, v_val_1620_, v_traces_1676_, v___x_1677_);
lean_dec_ref(v_traces_1676_);
v___x_1679_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1680_, 0, v___x_1621_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
lean_ctor_set(v___x_1680_, 2, v___x_1622_);
lean_ctor_set(v___x_1680_, 3, v___x_1614_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*4, v_val_1620_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1642_);
v___x_1682_ = lean_task_pure(v___x_1681_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec_ref_known(v___x_1673_, 1);
lean_dec(v___x_1644_);
lean_dec(v___x_1622_);
lean_dec_ref(v___x_1621_);
lean_dec_ref(v___x_1614_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1623_);
lean_ctor_set(v___x_1683_, 1, v___x_1642_);
v___x_1684_ = lean_task_pure(v___x_1683_);
return v___x_1684_;
}
}
v___jp_1685_:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_bool_not(v___y_1686_);
if (v___x_1687_ == 0)
{
lean_inc(v___x_1644_);
lean_inc(v___x_1608_);
lean_inc(v___x_1610_);
lean_inc_ref(v_fileMap_1649_);
lean_inc_ref(v_fileName_1648_);
v_fileName_1656_ = v_fileName_1648_;
v_fileMap_1657_ = v_fileMap_1649_;
v_currRecDepth_1658_ = v___x_1610_;
v_ref_1659_ = v___x_1651_;
v_currNamespace_1660_ = v___x_1608_;
v_openDecls_1661_ = v___x_1632_;
v_initHeartbeats_1662_ = v___x_1610_;
v_maxHeartbeats_1663_ = v___x_1652_;
v_quotContext_1664_ = v___x_1608_;
v_currMacroScope_1665_ = v___x_1628_;
v_cancelTk_x3f_1666_ = v___x_1624_;
v_suppressElabErrors_1667_ = v_val_1620_;
v_inheritedTraceOptions_1668_ = v___x_1645_;
v___y_1669_ = v___x_1644_;
goto v___jp_1655_;
}
else
{
lean_object* v___x_1688_; lean_object* v_env_1689_; lean_object* v_nextMacroScope_1690_; lean_object* v_ngen_1691_; lean_object* v_auxDeclNGen_1692_; lean_object* v_traceState_1693_; lean_object* v_messages_1694_; lean_object* v_infoState_1695_; lean_object* v_snapshotTasks_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1705_; 
v___x_1688_ = lean_st_ref_take(v___x_1644_);
v_env_1689_ = lean_ctor_get(v___x_1688_, 0);
v_nextMacroScope_1690_ = lean_ctor_get(v___x_1688_, 1);
v_ngen_1691_ = lean_ctor_get(v___x_1688_, 2);
v_auxDeclNGen_1692_ = lean_ctor_get(v___x_1688_, 3);
v_traceState_1693_ = lean_ctor_get(v___x_1688_, 4);
v_messages_1694_ = lean_ctor_get(v___x_1688_, 6);
v_infoState_1695_ = lean_ctor_get(v___x_1688_, 7);
v_snapshotTasks_1696_ = lean_ctor_get(v___x_1688_, 8);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v___x_1688_, 5);
lean_dec(v_unused_1706_);
v___x_1698_ = v___x_1688_;
v_isShared_1699_ = v_isSharedCheck_1705_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snapshotTasks_1696_);
lean_inc(v_infoState_1695_);
lean_inc(v_messages_1694_);
lean_inc(v_traceState_1693_);
lean_inc(v_auxDeclNGen_1692_);
lean_inc(v_ngen_1691_);
lean_inc(v_nextMacroScope_1690_);
lean_inc(v_env_1689_);
lean_dec(v___x_1688_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1705_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = l_Lean_Kernel_enableDiag(v_env_1689_, v___x_1654_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 5, v___x_1635_);
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_nextMacroScope_1690_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_ngen_1691_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_auxDeclNGen_1692_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_traceState_1693_);
lean_ctor_set(v_reuseFailAlloc_1704_, 5, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1704_, 6, v_messages_1694_);
lean_ctor_set(v_reuseFailAlloc_1704_, 7, v_infoState_1695_);
lean_ctor_set(v_reuseFailAlloc_1704_, 8, v_snapshotTasks_1696_);
v___x_1702_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_st_ref_set(v___x_1644_, v___x_1702_);
lean_inc(v___x_1644_);
lean_inc(v___x_1608_);
lean_inc(v___x_1610_);
lean_inc_ref(v_fileMap_1649_);
lean_inc_ref(v_fileName_1648_);
v_fileName_1656_ = v_fileName_1648_;
v_fileMap_1657_ = v_fileMap_1649_;
v_currRecDepth_1658_ = v___x_1610_;
v_ref_1659_ = v___x_1651_;
v_currNamespace_1660_ = v___x_1608_;
v_openDecls_1661_ = v___x_1632_;
v_initHeartbeats_1662_ = v___x_1610_;
v_maxHeartbeats_1663_ = v___x_1652_;
v_quotContext_1664_ = v___x_1608_;
v_currMacroScope_1665_ = v___x_1628_;
v_cancelTk_x3f_1666_ = v___x_1624_;
v_suppressElabErrors_1667_ = v_val_1620_;
v_inheritedTraceOptions_1668_ = v___x_1645_;
v___y_1669_ = v___x_1644_;
goto v___jp_1655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed(lean_object** _args){
lean_object* v___x_1708_ = _args[0];
lean_object* v___x_1709_ = _args[1];
lean_object* v___x_1710_ = _args[2];
lean_object* v___x_1711_ = _args[3];
lean_object* v___x_1712_ = _args[4];
lean_object* v_env_1713_ = _args[5];
lean_object* v___x_1714_ = _args[6];
lean_object* v___x_1715_ = _args[7];
lean_object* v_a_1716_ = _args[8];
lean_object* v_opts_1717_ = _args[9];
lean_object* v___x_1718_ = _args[10];
lean_object* v_pos_1719_ = _args[11];
lean_object* v_val_1720_ = _args[12];
lean_object* v___x_1721_ = _args[13];
lean_object* v___x_1722_ = _args[14];
lean_object* v___x_1723_ = _args[15];
lean_object* v___x_1724_ = _args[16];
lean_object* v___x_1725_ = _args[17];
lean_object* v_x_1726_ = _args[18];
lean_object* v___y_1727_ = _args[19];
_start:
{
size_t v___x_44899__boxed_1728_; uint8_t v___x_44900__boxed_1729_; uint8_t v_val_44904__boxed_1730_; uint8_t v___x_44909__boxed_1731_; lean_object* v_res_1732_; 
v___x_44899__boxed_1728_ = lean_unbox_usize(v___x_1711_);
lean_dec(v___x_1711_);
v___x_44900__boxed_1729_ = lean_unbox(v___x_1712_);
v_val_44904__boxed_1730_ = lean_unbox(v_val_1720_);
v___x_44909__boxed_1731_ = lean_unbox(v___x_1725_);
v_res_1732_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3(v___x_1708_, v___x_1709_, v___x_1710_, v___x_44899__boxed_1728_, v___x_44900__boxed_1729_, v_env_1713_, v___x_1714_, v___x_1715_, v_a_1716_, v_opts_1717_, v___x_1718_, v_pos_1719_, v_val_44904__boxed_1730_, v___x_1721_, v___x_1722_, v___x_1723_, v___x_1724_, v___x_44909__boxed_1731_, v_x_1726_);
lean_dec(v_pos_1719_);
lean_dec_ref(v_a_1716_);
lean_dec(v___x_1715_);
lean_dec(v___x_1709_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(lean_object* v_a_1733_, lean_object* v___x_1734_, lean_object* v_parserState_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v_toProcessingContext_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_toProcessingContext_1737_ = lean_ctor_get(v_a_1733_, 0);
v___x_1738_ = l_Lean_MessageLog_empty;
lean_inc_ref(v_toProcessingContext_1737_);
v___x_1739_ = l_Lean_Parser_parseCommand(v_toProcessingContext_1737_, v___x_1734_, v_parserState_1735_, v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed(lean_object* v_a_1740_, lean_object* v___x_1741_, lean_object* v_parserState_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2(v_a_1740_, v___x_1741_, v_parserState_1742_, v_x_1743_);
lean_dec_ref(v_a_1740_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(lean_object* v_as_1746_, size_t v_i_1747_, size_t v_stop_1748_, lean_object* v_b_1749_){
_start:
{
uint8_t v___x_1751_; 
v___x_1751_ = lean_usize_dec_eq(v_i_1747_, v_stop_1748_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; size_t v___x_1755_; size_t v___x_1756_; 
v___x_1752_ = lean_array_uget_borrowed(v_as_1746_, v_i_1747_);
v___f_1753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___closed__0));
lean_inc(v___x_1752_);
v___x_1754_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___f_1753_, v___x_1752_);
v___x_1755_ = ((size_t)1ULL);
v___x_1756_ = lean_usize_add(v_i_1747_, v___x_1755_);
v_i_1747_ = v___x_1756_;
v_b_1749_ = v___x_1754_;
goto _start;
}
else
{
return v_b_1749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg___boxed(lean_object* v_as_1758_, lean_object* v_i_1759_, lean_object* v_stop_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_i_boxed_1763_; size_t v_stop_boxed_1764_; lean_object* v_res_1765_; 
v_i_boxed_1763_ = lean_unbox_usize(v_i_1759_);
lean_dec(v_i_1759_);
v_stop_boxed_1764_ = lean_unbox_usize(v_stop_1760_);
lean_dec(v_stop_1760_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_as_1758_, v_i_boxed_1763_, v_stop_boxed_1764_, v_b_1761_);
lean_dec_ref(v_as_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed(lean_object* v_oldResult_1766_, lean_object* v_cmds_1767_, lean_object* v_stx_1768_, lean_object* v_newParserState_1769_, lean_object* v_val_1770_, lean_object* v_sync_1771_, lean_object* v_val_1772_, lean_object* v_a_1773_, lean_object* v_oldNext_1774_, lean_object* v___y_1775_){
_start:
{
uint8_t v_sync_boxed_1776_; lean_object* v_res_1777_; 
v_sync_boxed_1776_ = lean_unbox(v_sync_1771_);
v_res_1777_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0(v_oldResult_1766_, v_cmds_1767_, v_stx_1768_, v_newParserState_1769_, v_val_1770_, v_sync_boxed_1776_, v_val_1772_, v_a_1773_, v_oldNext_1774_);
lean_dec_ref(v_a_1773_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(lean_object* v_val_1778_, lean_object* v_cmds_1779_, lean_object* v_stx_1780_, lean_object* v_newParserState_1781_, lean_object* v_val_1782_, uint8_t v_sync_1783_, lean_object* v_val_1784_, lean_object* v_a_1785_, lean_object* v_oldResult_1786_){
_start:
{
lean_object* v_task_1788_; lean_object* v___x_1789_; lean_object* v___f_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; 
v_task_1788_ = lean_ctor_get(v_val_1778_, 3);
lean_inc_ref(v_task_1788_);
lean_dec_ref(v_val_1778_);
v___x_1789_ = lean_box(v_sync_1783_);
lean_inc_ref(v_a_1785_);
v___f_1790_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__0___boxed), 10, 8);
lean_closure_set(v___f_1790_, 0, v_oldResult_1786_);
lean_closure_set(v___f_1790_, 1, v_cmds_1779_);
lean_closure_set(v___f_1790_, 2, v_stx_1780_);
lean_closure_set(v___f_1790_, 3, v_newParserState_1781_);
lean_closure_set(v___f_1790_, 4, v_val_1782_);
lean_closure_set(v___f_1790_, 5, v___x_1789_);
lean_closure_set(v___f_1790_, 6, v_val_1784_);
lean_closure_set(v___f_1790_, 7, v_a_1785_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = 1;
v___x_1793_ = l_BaseIO_chainTask___redArg(v_task_1788_, v___f_1790_, v___x_1791_, v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed(lean_object* v_val_1794_, lean_object* v_cmds_1795_, lean_object* v_stx_1796_, lean_object* v_newParserState_1797_, lean_object* v_val_1798_, lean_object* v_sync_1799_, lean_object* v_val_1800_, lean_object* v_a_1801_, lean_object* v_oldResult_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v_sync_boxed_1804_; lean_object* v_res_1805_; 
v_sync_boxed_1804_ = lean_unbox(v_sync_1799_);
v_res_1805_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1(v_val_1794_, v_cmds_1795_, v_stx_1796_, v_newParserState_1797_, v_val_1798_, v_sync_boxed_1804_, v_val_1800_, v_a_1801_, v_oldResult_1802_);
lean_dec_ref(v_a_1801_);
return v_res_1805_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = l_Lean_Language_instInhabitedDynamicSnapshot;
v___x_1808_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1807_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l_Lean_Language_instInhabitedSnapshotTree_default;
v___x_1810_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_1809_);
return v___x_1810_;
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(lean_object* v___x_1824_, lean_object* v_val_1825_, lean_object* v_cmds_1826_, lean_object* v_fst_1827_, lean_object* v_fst_1828_, uint8_t v_val_1829_, lean_object* v_a_1830_, lean_object* v_snd_1831_, lean_object* v___x_1832_, uint8_t v___x_1833_, lean_object* v_fst_1834_, lean_object* v_val_1835_, lean_object* v_val_1836_, lean_object* v_val_1837_, lean_object* v_snd_1838_, lean_object* v_prom_1839_, lean_object* v___x_1840_, lean_object* v___f_1841_, lean_object* v___f_1842_, lean_object* v___f_1843_, lean_object* v_pos_1844_, lean_object* v_cmdState_1845_, lean_object* v_opts_1846_, lean_object* v___x_1847_, lean_object* v_old_x3f_1848_, lean_object* v_parseCancelTk_1849_, lean_object* v_next_x3f_1850_){
_start:
{
lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v_snapshotTasks_1858_; lean_object* v_traceTask_1859_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; size_t v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v_env_1893_; lean_object* v_messages_1894_; lean_object* v_scopes_1895_; lean_object* v_infoState_1896_; lean_object* v_traceState_1897_; lean_object* v_snapshotTasks_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v_reportedCmdState_1909_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; size_t v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_reportedCmdState_1966_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; size_t v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; size_t v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_2030_; 
if (lean_obj_tag(v_next_x3f_1850_) == 0)
{
lean_object* v___x_2083_; 
lean_dec_ref(v_parseCancelTk_1849_);
v___x_2083_ = lean_box(0);
v___y_2030_ = v___x_2083_;
goto v___jp_2029_;
}
else
{
lean_object* v_toProcessingContext_2084_; lean_object* v_val_2085_; lean_object* v_pos_2086_; lean_object* v_endPos_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_toProcessingContext_2084_ = lean_ctor_get(v_a_1830_, 0);
v_val_2085_ = lean_ctor_get(v_next_x3f_1850_, 0);
v_pos_2086_ = lean_ctor_get(v_fst_1828_, 0);
v_endPos_2087_ = lean_ctor_get(v_toProcessingContext_2084_, 3);
v___x_2088_ = lean_box(0);
lean_inc(v_endPos_2087_);
lean_inc(v_pos_2086_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v_pos_2086_);
lean_ctor_set(v___x_2089_, 1, v_endPos_2087_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_parseCancelTk_1849_);
v___x_2092_ = l_IO_Promise_result_x21___redArg(v_val_2085_);
v___x_2093_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2088_);
lean_ctor_set(v___x_2093_, 1, v___x_2090_);
lean_ctor_set(v___x_2093_, 2, v___x_2091_);
lean_ctor_set(v___x_2093_, 3, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
v___y_2030_ = v___x_2094_;
goto v___jp_2029_;
}
v___jp_1852_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1860_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1860_, 0, v___y_1856_);
lean_ctor_set(v___x_1860_, 1, v___x_1824_);
lean_ctor_set(v___x_1860_, 2, v___y_1855_);
lean_ctor_set(v___x_1860_, 3, v_traceTask_1859_);
v___x_1861_ = lean_array_push(v_snapshotTasks_1858_, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___y_1854_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_io_promise_resolve(v___x_1862_, v_val_1825_);
if (lean_obj_tag(v_next_x3f_1850_) == 1)
{
lean_object* v_val_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v_val_1864_ = lean_ctor_get(v_next_x3f_1850_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v_next_x3f_1850_, 1);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_array_push(v_cmds_1826_, v_fst_1827_);
v___x_1867_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_1865_, v_fst_1828_, v___y_1857_, v_val_1864_, v_val_1829_, v___y_1853_, v___x_1866_, v_a_1830_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; 
lean_dec_ref(v___y_1857_);
lean_dec_ref(v___y_1853_);
lean_dec(v_next_x3f_1850_);
lean_dec_ref(v_fst_1828_);
lean_dec(v_fst_1827_);
lean_dec_ref(v_cmds_1826_);
v___x_1868_ = lean_box(0);
return v___x_1868_;
}
}
v___jp_1869_:
{
lean_object* v_snapshotTasks_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_snapshotTasks_1876_ = lean_ctor_get(v___y_1874_, 10);
lean_inc_ref(v_snapshotTasks_1876_);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___y_1875_);
lean_dec(v___y_1875_);
lean_inc_ref(v___y_1871_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___y_1871_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_task_pure(v___x_1878_);
v___y_1853_ = v___y_1870_;
v___y_1854_ = v___y_1871_;
v___y_1855_ = v___y_1872_;
v___y_1856_ = v___y_1873_;
v___y_1857_ = v___y_1874_;
v_snapshotTasks_1858_ = v_snapshotTasks_1876_;
v_traceTask_1859_ = v___x_1879_;
goto v___jp_1852_;
}
v___jp_1880_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_opts_1919_; uint8_t v_hasTrace_1920_; 
v___x_1910_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_1894_);
v___x_1911_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1911_, 0, v___y_1901_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
lean_ctor_set(v___x_1911_, 2, v___y_1902_);
lean_ctor_set(v___x_1911_, 3, v_traceState_1897_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*4, v_val_1829_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v_reportedCmdState_1909_);
v___x_1913_ = lean_io_promise_resolve(v___x_1912_, v_val_1836_);
v___x_1914_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1896_);
lean_inc(v___y_1900_);
v___x_1915_ = l_BaseIO_chainTask___redArg(v___x_1914_, v___y_1905_, v___y_1900_, v___x_1833_);
v___x_1916_ = l_Lean_inheritedTraceOptions;
v___x_1917_ = lean_st_ref_get(v___x_1916_);
v___x_1918_ = l_List_head_x21___redArg(v___x_1840_, v_scopes_1895_);
lean_dec(v_scopes_1895_);
lean_dec_ref(v___x_1840_);
v_opts_1919_ = lean_ctor_get(v___x_1918_, 1);
lean_inc_ref(v_opts_1919_);
lean_dec(v___x_1918_);
v_hasTrace_1920_ = lean_ctor_get_uint8(v_opts_1919_, sizeof(void*)*1);
if (v_hasTrace_1920_ == 0)
{
lean_dec_ref(v_opts_1919_);
lean_dec(v___x_1917_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v_snapshotTasks_1898_);
lean_dec_ref(v_env_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_pos_1844_);
lean_dec_ref(v___f_1843_);
lean_dec_ref(v___f_1842_);
lean_dec_ref(v___f_1841_);
lean_dec(v___x_1832_);
v___y_1870_ = v___y_1903_;
v___y_1871_ = v___y_1889_;
v___y_1872_ = v___y_1890_;
v___y_1873_ = v___y_1906_;
v___y_1874_ = v___y_1892_;
v___y_1875_ = v___y_1900_;
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
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v___y_1904_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v_snapshotTasks_1898_);
lean_dec_ref(v_env_1893_);
lean_dec(v___y_1891_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v_pos_1844_);
lean_dec_ref(v___f_1843_);
lean_dec_ref(v___f_1842_);
lean_dec_ref(v___f_1841_);
lean_dec(v___x_1832_);
v___y_1870_ = v___y_1903_;
v___y_1871_ = v___y_1889_;
v___y_1872_ = v___y_1890_;
v___y_1873_ = v___y_1906_;
v___y_1874_ = v___y_1892_;
v___y_1875_ = v___y_1900_;
goto v___jp_1869_;
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; 
lean_inc_n(v___y_1900_, 3);
v___x_1923_ = lean_task_map(v___f_1841_, v___y_1907_, v___y_1900_, v___x_1833_);
lean_inc_n(v___y_1890_, 3);
lean_inc_n(v___y_1908_, 2);
lean_inc_n(v___y_1891_, 2);
v___x_1924_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1924_, 0, v___y_1891_);
lean_ctor_set(v___x_1924_, 1, v___y_1908_);
lean_ctor_set(v___x_1924_, 2, v___y_1890_);
lean_ctor_set(v___x_1924_, 3, v___x_1923_);
v___x_1925_ = lean_task_map(v___f_1842_, v___y_1904_, v___y_1900_, v___x_1833_);
v___x_1926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1891_);
lean_ctor_set(v___x_1926_, 1, v___y_1908_);
lean_ctor_set(v___x_1926_, 2, v___y_1890_);
lean_ctor_set(v___x_1926_, 3, v___x_1925_);
v___x_1927_ = lean_task_map(v___f_1843_, v___y_1899_, v___y_1900_, v___x_1833_);
v___x_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1928_, 0, v___y_1891_);
lean_ctor_set(v___x_1928_, 1, v___y_1908_);
lean_ctor_set(v___x_1928_, 2, v___y_1890_);
lean_ctor_set(v___x_1928_, 3, v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(3u);
v___x_1930_ = lean_mk_empty_array_with_capacity(v___x_1929_);
v___x_1931_ = lean_array_push(v___x_1930_, v___x_1924_);
v___x_1932_ = lean_array_push(v___x_1931_, v___x_1926_);
v___x_1933_ = lean_array_push(v___x_1932_, v___x_1928_);
v___x_1934_ = l_Array_append___redArg(v___x_1933_, v_snapshotTasks_1898_);
lean_inc_ref(v___y_1889_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___y_1889_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
lean_inc_ref(v___x_1935_);
v___x_1936_ = l_Lean_Language_SnapshotTree_waitAll(v___x_1935_);
v___x_1937_ = lean_box_usize(v___y_1887_);
v___x_1938_ = lean_box(v___x_1833_);
v___x_1939_ = lean_box(v_val_1829_);
v___x_1940_ = lean_box(v___x_1922_);
lean_inc_ref(v_a_1830_);
lean_inc_ref(v___y_1888_);
v___f_1941_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_1941_, 0, v___x_1832_);
lean_closure_set(v___f_1941_, 1, v___y_1883_);
lean_closure_set(v___f_1941_, 2, v___y_1885_);
lean_closure_set(v___f_1941_, 3, v___x_1937_);
lean_closure_set(v___f_1941_, 4, v___x_1938_);
lean_closure_set(v___f_1941_, 5, v_env_1893_);
lean_closure_set(v___f_1941_, 6, v___y_1888_);
lean_closure_set(v___f_1941_, 7, v___x_1916_);
lean_closure_set(v___f_1941_, 8, v_a_1830_);
lean_closure_set(v___f_1941_, 9, v_opts_1919_);
lean_closure_set(v___f_1941_, 10, v___x_1935_);
lean_closure_set(v___f_1941_, 11, v_pos_1844_);
lean_closure_set(v___f_1941_, 12, v___x_1939_);
lean_closure_set(v___f_1941_, 13, v___y_1881_);
lean_closure_set(v___f_1941_, 14, v___y_1886_);
lean_closure_set(v___f_1941_, 15, v___y_1882_);
lean_closure_set(v___f_1941_, 16, v___y_1884_);
lean_closure_set(v___f_1941_, 17, v___x_1940_);
v___x_1942_ = lean_io_bind_task(v___x_1936_, v___f_1941_, v___y_1900_, v_val_1829_);
v___y_1853_ = v___y_1903_;
v___y_1854_ = v___y_1889_;
v___y_1855_ = v___y_1890_;
v___y_1856_ = v___y_1906_;
v___y_1857_ = v___y_1892_;
v_snapshotTasks_1858_ = v_snapshotTasks_1898_;
v_traceTask_1859_ = v___x_1942_;
goto v___jp_1852_;
}
}
}
v___jp_1943_:
{
lean_object* v_env_1967_; lean_object* v_messages_1968_; lean_object* v_scopes_1969_; lean_object* v_infoState_1970_; lean_object* v_traceState_1971_; lean_object* v_snapshotTasks_1972_; 
v_env_1967_ = lean_ctor_get(v___y_1955_, 0);
lean_inc_ref(v_env_1967_);
v_messages_1968_ = lean_ctor_get(v___y_1955_, 1);
lean_inc_ref(v_messages_1968_);
v_scopes_1969_ = lean_ctor_get(v___y_1955_, 2);
lean_inc(v_scopes_1969_);
v_infoState_1970_ = lean_ctor_get(v___y_1955_, 8);
lean_inc_ref(v_infoState_1970_);
v_traceState_1971_ = lean_ctor_get(v___y_1955_, 9);
lean_inc_ref(v_traceState_1971_);
v_snapshotTasks_1972_ = lean_ctor_get(v___y_1955_, 10);
lean_inc_ref(v_snapshotTasks_1972_);
v___y_1881_ = v___y_1944_;
v___y_1882_ = v___y_1946_;
v___y_1883_ = v___y_1945_;
v___y_1884_ = v___y_1947_;
v___y_1885_ = v___y_1948_;
v___y_1886_ = v___y_1949_;
v___y_1887_ = v___y_1950_;
v___y_1888_ = v___y_1951_;
v___y_1889_ = v___y_1952_;
v___y_1890_ = v___y_1953_;
v___y_1891_ = v___y_1954_;
v___y_1892_ = v___y_1955_;
v_env_1893_ = v_env_1967_;
v_messages_1894_ = v_messages_1968_;
v_scopes_1895_ = v_scopes_1969_;
v_infoState_1896_ = v_infoState_1970_;
v_traceState_1897_ = v_traceState_1971_;
v_snapshotTasks_1898_ = v_snapshotTasks_1972_;
v___y_1899_ = v___y_1956_;
v___y_1900_ = v___y_1957_;
v___y_1901_ = v___y_1958_;
v___y_1902_ = v___y_1959_;
v___y_1903_ = v___y_1960_;
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
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___f_2002_; uint8_t v___x_2003_; 
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___y_1997_);
lean_ctor_set(v___x_1998_, 1, v_val_1835_);
lean_inc_ref(v___y_1991_);
lean_inc_n(v_pos_1844_, 2);
lean_inc_ref(v_cmds_1826_);
lean_inc(v_fst_1827_);
v___x_1999_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_1827_, v_cmds_1826_, v_cmdState_1845_, v_pos_1844_, v___x_1998_, v___y_1991_, v_a_1830_);
v___x_2000_ = lean_box(v_val_1829_);
v___x_2001_ = lean_box(v___x_1833_);
lean_inc_ref(v_a_1830_);
lean_inc(v___y_1978_);
lean_inc_ref(v___x_1840_);
lean_inc_ref(v___x_1999_);
lean_inc_ref(v___y_1981_);
lean_inc_ref(v___y_1974_);
v___f_2002_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 12, 10);
lean_closure_set(v___f_2002_, 0, v___y_1974_);
lean_closure_set(v___f_2002_, 1, v___y_1981_);
lean_closure_set(v___f_2002_, 2, v___x_2000_);
lean_closure_set(v___f_2002_, 3, v_val_1837_);
lean_closure_set(v___f_2002_, 4, v___x_1999_);
lean_closure_set(v___f_2002_, 5, v___x_1840_);
lean_closure_set(v___f_2002_, 6, v___y_1978_);
lean_closure_set(v___f_2002_, 7, v___x_2001_);
lean_closure_set(v___f_2002_, 8, v_a_1830_);
lean_closure_set(v___f_2002_, 9, v_pos_1844_);
v___x_2003_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_1846_, v___x_1847_);
if (v___x_2003_ == 0)
{
lean_dec(v___y_1989_);
lean_inc_ref(v___x_1999_);
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1976_;
v___y_1946_ = v___y_1975_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___x_1999_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___f_2002_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v_reportedCmdState_1966_ = v___x_1999_;
goto v___jp_1943_;
}
else
{
uint8_t v___x_2004_; uint8_t v___x_2005_; 
lean_inc(v_fst_1827_);
v___x_2004_ = l_Lean_Parser_isTerminalCommand(v_fst_1827_);
v___x_2005_ = lean_bool_not(v___x_2004_);
if (v___x_2005_ == 0)
{
lean_dec(v___y_1989_);
lean_inc_ref(v___x_1999_);
v___y_1944_ = v___y_1974_;
v___y_1945_ = v___y_1976_;
v___y_1946_ = v___y_1975_;
v___y_1947_ = v___y_1977_;
v___y_1948_ = v___y_1978_;
v___y_1949_ = v___y_1979_;
v___y_1950_ = v___y_1980_;
v___y_1951_ = v___y_1981_;
v___y_1952_ = v___y_1982_;
v___y_1953_ = v___y_1983_;
v___y_1954_ = v___y_1985_;
v___y_1955_ = v___x_1999_;
v___y_1956_ = v___y_1986_;
v___y_1957_ = v___y_1987_;
v___y_1958_ = v___y_1988_;
v___y_1959_ = v___y_1990_;
v___y_1960_ = v___y_1991_;
v___y_1961_ = v___y_1992_;
v___y_1962_ = v___f_2002_;
v___y_1963_ = v___y_1994_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1996_;
v_reportedCmdState_1966_ = v___x_1999_;
goto v___jp_1943_;
}
else
{
lean_object* v_env_2006_; lean_object* v_messages_2007_; lean_object* v_scopes_2008_; lean_object* v_infoState_2009_; lean_object* v_traceState_2010_; lean_object* v_snapshotTasks_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_env_2006_ = lean_ctor_get(v___x_1999_, 0);
lean_inc_ref_n(v_env_2006_, 2);
v_messages_2007_ = lean_ctor_get(v___x_1999_, 1);
lean_inc_ref(v_messages_2007_);
v_scopes_2008_ = lean_ctor_get(v___x_1999_, 2);
lean_inc(v_scopes_2008_);
v_infoState_2009_ = lean_ctor_get(v___x_1999_, 8);
lean_inc_ref(v_infoState_2009_);
v_traceState_2010_ = lean_ctor_get(v___x_1999_, 9);
lean_inc_ref(v_traceState_2010_);
v_snapshotTasks_2011_ = lean_ctor_get(v___x_1999_, 10);
lean_inc_ref(v_snapshotTasks_2011_);
v___x_2012_ = lean_mk_empty_array_with_capacity(v___y_1989_);
lean_dec(v___y_1989_);
lean_inc_ref(v___x_2012_);
v___x_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_inc_n(v___y_1987_, 3);
v___x_2014_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___x_2012_);
lean_ctor_set(v___x_2014_, 2, v___y_1987_);
lean_ctor_set(v___x_2014_, 3, v___y_1987_);
lean_ctor_set_usize(v___x_2014_, 4, v___y_1984_);
v___x_2015_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2014_, 2);
v___x_2016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2014_);
lean_ctor_set(v___x_2016_, 2, v___x_2015_);
v___x_2017_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2018_ = l_Lean_Options_empty;
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_mk_empty_array_with_capacity(v___y_1987_);
lean_inc_ref_n(v___x_2020_, 2);
lean_inc_n(v___x_1832_, 2);
v___x_2021_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2021_, 0, v___x_2017_);
lean_ctor_set(v___x_2021_, 1, v___x_2018_);
lean_ctor_set(v___x_2021_, 2, v___x_1832_);
lean_ctor_set(v___x_2021_, 3, v___x_2019_);
lean_ctor_set(v___x_2021_, 4, v___x_2019_);
lean_ctor_set(v___x_2021_, 5, v___x_2020_);
lean_ctor_set(v___x_2021_, 6, v___x_2020_);
lean_ctor_set(v___x_2021_, 7, v___x_2019_);
lean_ctor_set(v___x_2021_, 8, v___x_2019_);
lean_ctor_set(v___x_2021_, 9, v___x_2019_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*10, v_val_1829_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*10 + 1, v_val_1829_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*10 + 2, v_val_1829_);
v___x_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
lean_ctor_set(v___x_2022_, 1, v___x_2019_);
v___x_2023_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2024_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2025_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_1832_);
v___x_2026_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2027_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
lean_ctor_set(v___x_2027_, 2, v___x_2014_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*3, v___x_1833_);
lean_inc_ref(v___y_1993_);
v___x_2028_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2028_, 0, v_env_2006_);
lean_ctor_set(v___x_2028_, 1, v___x_2016_);
lean_ctor_set(v___x_2028_, 2, v___x_2022_);
lean_ctor_set(v___x_2028_, 3, v___x_2015_);
lean_ctor_set(v___x_2028_, 4, v___x_2023_);
lean_ctor_set(v___x_2028_, 5, v___y_1987_);
lean_ctor_set(v___x_2028_, 6, v___x_2024_);
lean_ctor_set(v___x_2028_, 7, v___x_2025_);
lean_ctor_set(v___x_2028_, 8, v___x_2027_);
lean_ctor_set(v___x_2028_, 9, v___y_1993_);
lean_ctor_set(v___x_2028_, 10, v___x_2020_);
v___y_1881_ = v___y_1974_;
v___y_1882_ = v___y_1975_;
v___y_1883_ = v___y_1976_;
v___y_1884_ = v___y_1977_;
v___y_1885_ = v___y_1978_;
v___y_1886_ = v___y_1979_;
v___y_1887_ = v___y_1980_;
v___y_1888_ = v___y_1981_;
v___y_1889_ = v___y_1982_;
v___y_1890_ = v___y_1983_;
v___y_1891_ = v___y_1985_;
v___y_1892_ = v___x_1999_;
v_env_1893_ = v_env_2006_;
v_messages_1894_ = v_messages_2007_;
v_scopes_1895_ = v_scopes_2008_;
v_infoState_1896_ = v_infoState_2009_;
v_traceState_1897_ = v_traceState_2010_;
v_snapshotTasks_1898_ = v_snapshotTasks_2011_;
v___y_1899_ = v___y_1986_;
v___y_1900_ = v___y_1987_;
v___y_1901_ = v___y_1988_;
v___y_1902_ = v___y_1990_;
v___y_1903_ = v___y_1991_;
v___y_1904_ = v___y_1992_;
v___y_1905_ = v___f_2002_;
v___y_1906_ = v___y_1994_;
v___y_1907_ = v___y_1995_;
v___y_1908_ = v___y_1996_;
v_reportedCmdState_1909_ = v___x_2028_;
goto v___jp_1880_;
}
}
}
v___jp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2031_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_1831_);
v___x_2032_ = l_IO_CancelToken_new();
v___x_2033_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_1832_);
v___x_2034_ = l_Lean_Name_str___override(v___x_1832_, v___x_2033_);
v___x_2035_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2036_ = l_Lean_Name_str___override(v___x_2034_, v___x_2035_);
v___x_2037_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2038_ = l_Lean_Name_str___override(v___x_2036_, v___x_2037_);
v___x_2039_ = l_Lean_Name_str___override(v___x_2038_, v___x_2035_);
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = l_Lean_Name_num___override(v___x_2039_, v___x_2040_);
v___x_2042_ = l_Lean_Name_str___override(v___x_2041_, v___x_2035_);
v___x_2043_ = l_Lean_Name_str___override(v___x_2042_, v___x_2037_);
v___x_2044_ = l_Lean_Name_str___override(v___x_2043_, v___x_2035_);
v___x_2045_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2046_ = l_Lean_Name_str___override(v___x_2044_, v___x_2045_);
v___x_2047_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2048_ = l_Lean_Name_str___override(v___x_2046_, v___x_2047_);
v___x_2049_ = l_Lean_Name_toString(v___x_2048_, v___x_1833_);
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_unsigned_to_nat(32u);
v___x_2052_ = ((size_t)5ULL);
v___x_2053_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2049_, 2);
v___x_2054_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2054_, 0, v___x_2049_);
lean_ctor_set(v___x_2054_, 1, v___x_2031_);
lean_ctor_set(v___x_2054_, 2, v___x_2050_);
lean_ctor_set(v___x_2054_, 3, v___x_2053_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*4, v_val_1829_);
v___x_2055_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2056_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2056_, 0, v___x_2049_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
lean_ctor_set(v___x_2056_, 2, v___x_2050_);
lean_ctor_set(v___x_2056_, 3, v___x_2053_);
lean_ctor_set_uint8(v___x_2056_, sizeof(void*)*4, v_val_1829_);
lean_inc(v_fst_1834_);
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_fst_1834_);
v___x_2058_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2057_);
lean_inc_ref(v___x_2032_);
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2032_);
v___x_2060_ = l_IO_Promise_result_x21___redArg(v_val_1835_);
lean_inc_ref(v___x_2060_);
lean_inc(v___x_2058_);
lean_inc_ref_n(v___x_2057_, 3);
v___x_2061_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2057_);
lean_ctor_set(v___x_2061_, 1, v___x_2058_);
lean_ctor_set(v___x_2061_, 2, v___x_2059_);
lean_ctor_set(v___x_2061_, 3, v___x_2060_);
v___x_2062_ = l_IO_Promise_result_x21___redArg(v_val_1836_);
lean_inc_ref(v___x_2062_);
lean_inc_n(v___x_1824_, 3);
v___x_2063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2057_);
lean_ctor_set(v___x_2063_, 1, v___x_1824_);
lean_ctor_set(v___x_2063_, 2, v___x_2050_);
lean_ctor_set(v___x_2063_, 3, v___x_2062_);
v___x_2064_ = l_IO_Promise_result_x21___redArg(v_val_1837_);
lean_inc_ref(v___x_2064_);
v___x_2065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2057_);
lean_ctor_set(v___x_2065_, 1, v___x_1824_);
lean_ctor_set(v___x_2065_, 2, v___x_2050_);
lean_ctor_set(v___x_2065_, 3, v___x_2064_);
v___x_2066_ = l_IO_Promise_result_x21___redArg(v_val_1825_);
v___x_2067_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2050_);
lean_ctor_set(v___x_2067_, 1, v___x_1824_);
lean_ctor_set(v___x_2067_, 2, v___x_2050_);
lean_ctor_set(v___x_2067_, 3, v___x_2066_);
lean_inc_ref(v___x_2056_);
v___x_2068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2056_);
lean_ctor_set(v___x_2068_, 1, v___x_2061_);
lean_ctor_set(v___x_2068_, 2, v___x_2063_);
lean_ctor_set(v___x_2068_, 3, v___x_2065_);
lean_ctor_set(v___x_2068_, 4, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2054_);
lean_ctor_set(v___x_2069_, 1, v_fst_1834_);
lean_ctor_set(v___x_2069_, 2, v_snd_1838_);
lean_ctor_set(v___x_2069_, 3, v___x_2068_);
lean_ctor_set(v___x_2069_, 4, v___y_2030_);
v___x_2070_ = lean_io_promise_resolve(v___x_2069_, v_prom_1839_);
if (lean_obj_tag(v_old_x3f_1848_) == 0)
{
lean_inc_ref(v___x_2056_);
lean_inc_ref(v___x_2049_);
v___y_1974_ = v___x_2049_;
v___y_1975_ = v___x_2056_;
v___y_1976_ = v___x_2051_;
v___y_1977_ = v___x_2050_;
v___y_1978_ = v___x_2040_;
v___y_1979_ = v___x_2050_;
v___y_1980_ = v___x_2052_;
v___y_1981_ = v___x_2053_;
v___y_1982_ = v___x_2056_;
v___y_1983_ = v___x_2050_;
v___y_1984_ = v___x_2052_;
v___y_1985_ = v___x_2057_;
v___y_1986_ = v___x_2064_;
v___y_1987_ = v___x_2040_;
v___y_1988_ = v___x_2049_;
v___y_1989_ = v___x_2051_;
v___y_1990_ = v___x_2050_;
v___y_1991_ = v___x_2032_;
v___y_1992_ = v___x_2062_;
v___y_1993_ = v___x_2053_;
v___y_1994_ = v___x_2050_;
v___y_1995_ = v___x_2060_;
v___y_1996_ = v___x_2058_;
v___y_1997_ = v___x_2050_;
goto v___jp_1973_;
}
else
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2082_; 
v_val_2071_ = lean_ctor_get(v_old_x3f_1848_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_old_x3f_1848_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2073_ = v_old_x3f_1848_;
v_isShared_2074_ = v_isSharedCheck_2082_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v_old_x3f_1848_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2082_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_elabSnap_2075_; lean_object* v_stx_2076_; lean_object* v_elabSnap_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v_elabSnap_2075_ = lean_ctor_get(v_val_2071_, 3);
lean_inc_ref(v_elabSnap_2075_);
v_stx_2076_ = lean_ctor_get(v_val_2071_, 1);
lean_inc(v_stx_2076_);
lean_dec(v_val_2071_);
v_elabSnap_2077_ = lean_ctor_get(v_elabSnap_2075_, 1);
lean_inc_ref(v_elabSnap_2077_);
lean_dec_ref(v_elabSnap_2075_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_stx_2076_);
lean_ctor_set(v___x_2078_, 1, v_elabSnap_2077_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2078_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_inc_ref(v___x_2056_);
lean_inc_ref(v___x_2049_);
v___y_1974_ = v___x_2049_;
v___y_1975_ = v___x_2056_;
v___y_1976_ = v___x_2051_;
v___y_1977_ = v___x_2050_;
v___y_1978_ = v___x_2040_;
v___y_1979_ = v___x_2050_;
v___y_1980_ = v___x_2052_;
v___y_1981_ = v___x_2053_;
v___y_1982_ = v___x_2056_;
v___y_1983_ = v___x_2050_;
v___y_1984_ = v___x_2052_;
v___y_1985_ = v___x_2057_;
v___y_1986_ = v___x_2064_;
v___y_1987_ = v___x_2040_;
v___y_1988_ = v___x_2049_;
v___y_1989_ = v___x_2051_;
v___y_1990_ = v___x_2050_;
v___y_1991_ = v___x_2032_;
v___y_1992_ = v___x_2062_;
v___y_1993_ = v___x_2053_;
v___y_1994_ = v___x_2050_;
v___y_1995_ = v___x_2060_;
v___y_1996_ = v___x_2058_;
v___y_1997_ = v___x_2080_;
goto v___jp_1973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(lean_object* v_cmds_2095_, lean_object* v_fst_2096_, lean_object* v_fst_2097_, uint8_t v_val_2098_, lean_object* v_a_2099_, lean_object* v_snd_2100_, lean_object* v___x_2101_, uint8_t v___x_2102_, lean_object* v_prom_2103_, lean_object* v___x_2104_, lean_object* v___f_2105_, lean_object* v___f_2106_, lean_object* v___f_2107_, lean_object* v_pos_2108_, lean_object* v_cmdState_2109_, lean_object* v_opts_2110_, lean_object* v_old_x3f_2111_, lean_object* v_parseCancelTk_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2119_; lean_object* v_snapshotTasks_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v_traceTask_2127_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; size_t v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v_env_2168_; lean_object* v_messages_2169_; lean_object* v_scopes_2170_; lean_object* v_infoState_2171_; lean_object* v_traceState_2172_; lean_object* v_snapshotTasks_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v_reportedCmdState_2181_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; size_t v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v_reportedCmdState_2240_; lean_object* v___x_2247_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; size_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; size_t v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v_fst_2385_; lean_object* v_snd_2386_; uint8_t v___y_2399_; uint8_t v___x_2402_; 
v___x_2114_ = lean_io_promise_new();
v___x_2115_ = lean_io_promise_new();
v___x_2116_ = lean_io_promise_new();
v___x_2117_ = lean_io_promise_new();
v___x_2247_ = l_Lean_internal_cmdlineSnapshots;
v___x_2402_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2110_, v___x_2247_);
if (v___x_2402_ == 0)
{
v___y_2399_ = v___x_2402_;
goto v___jp_2398_;
}
else
{
uint8_t v___x_2403_; uint8_t v___x_2404_; 
lean_inc(v_fst_2096_);
v___x_2403_ = l_Lean_Parser_isTerminalCommand(v_fst_2096_);
v___x_2404_ = lean_bool_not(v___x_2403_);
v___y_2399_ = v___x_2404_;
goto v___jp_2398_;
}
v___jp_2118_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2128_, 0, v___y_2124_);
lean_ctor_set(v___x_2128_, 1, v___y_2122_);
lean_ctor_set(v___x_2128_, 2, v___y_2125_);
lean_ctor_set(v___x_2128_, 3, v_traceTask_2127_);
v___x_2129_ = lean_array_push(v_snapshotTasks_2120_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___y_2126_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_io_promise_resolve(v___x_2130_, v___x_2117_);
lean_dec(v___x_2117_);
if (lean_obj_tag(v___y_2123_) == 1)
{
lean_object* v_val_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_val_2132_ = lean_ctor_get(v___y_2123_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v___y_2123_, 1);
v___x_2133_ = lean_box(0);
v___x_2134_ = lean_array_push(v_cmds_2095_, v_fst_2096_);
v___x_2135_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2133_, v_fst_2097_, v___y_2119_, v_val_2132_, v_val_2098_, v___y_2121_, v___x_2134_, v_a_2099_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2121_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v_fst_2097_);
lean_dec(v_fst_2096_);
lean_dec_ref(v_cmds_2095_);
v___x_2136_ = lean_box(0);
return v___x_2136_;
}
}
v___jp_2137_:
{
lean_object* v_snapshotTasks_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_snapshotTasks_2146_ = lean_ctor_get(v___y_2138_, 10);
lean_inc_ref(v_snapshotTasks_2146_);
v___x_2147_ = lean_mk_empty_array_with_capacity(v___y_2141_);
lean_dec(v___y_2141_);
lean_inc_ref(v___y_2145_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___y_2145_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = lean_task_pure(v___x_2148_);
v___y_2119_ = v___y_2138_;
v_snapshotTasks_2120_ = v_snapshotTasks_2146_;
v___y_2121_ = v___y_2139_;
v___y_2122_ = v___y_2140_;
v___y_2123_ = v___y_2143_;
v___y_2124_ = v___y_2142_;
v___y_2125_ = v___y_2144_;
v___y_2126_ = v___y_2145_;
v_traceTask_2127_ = v___x_2149_;
goto v___jp_2118_;
}
v___jp_2150_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v_opts_2191_; uint8_t v_hasTrace_2192_; 
v___x_2182_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_messages_2169_);
v___x_2183_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2183_, 0, v___y_2174_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
lean_ctor_set(v___x_2183_, 2, v___y_2175_);
lean_ctor_set(v___x_2183_, 3, v_traceState_2172_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*4, v_val_2098_);
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v_reportedCmdState_2181_);
v___x_2185_ = lean_io_promise_resolve(v___x_2184_, v___x_2115_);
lean_dec(v___x_2115_);
v___x_2186_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_2171_);
lean_inc(v___y_2163_);
v___x_2187_ = l_BaseIO_chainTask___redArg(v___x_2186_, v___y_2176_, v___y_2163_, v___x_2102_);
v___x_2188_ = l_Lean_inheritedTraceOptions;
v___x_2189_ = lean_st_ref_get(v___x_2188_);
v___x_2190_ = l_List_head_x21___redArg(v___x_2104_, v_scopes_2170_);
lean_dec(v_scopes_2170_);
lean_dec_ref(v___x_2104_);
v_opts_2191_ = lean_ctor_get(v___x_2190_, 1);
lean_inc_ref(v_opts_2191_);
lean_dec(v___x_2190_);
v_hasTrace_2192_ = lean_ctor_get_uint8(v_opts_2191_, sizeof(void*)*1);
if (v_hasTrace_2192_ == 0)
{
lean_dec_ref(v_opts_2191_);
lean_dec(v___x_2189_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_snapshotTasks_2173_);
lean_dec_ref(v_env_2168_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v_pos_2108_);
lean_dec_ref(v___f_2107_);
lean_dec_ref(v___f_2106_);
lean_dec_ref(v___f_2105_);
lean_dec(v___x_2101_);
v___y_2138_ = v___y_2167_;
v___y_2139_ = v___y_2160_;
v___y_2140_ = v___y_2162_;
v___y_2141_ = v___y_2163_;
v___y_2142_ = v___y_2177_;
v___y_2143_ = v___y_2178_;
v___y_2144_ = v___y_2179_;
v___y_2145_ = v___y_2165_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__2);
v___x_2194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___x_2189_, v_opts_2191_, v___x_2193_);
lean_dec(v___x_2189_);
if (v___x_2194_ == 0)
{
lean_dec_ref(v_opts_2191_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_snapshotTasks_2173_);
lean_dec_ref(v_env_2168_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v_pos_2108_);
lean_dec_ref(v___f_2107_);
lean_dec_ref(v___f_2106_);
lean_dec_ref(v___f_2105_);
lean_dec(v___x_2101_);
v___y_2138_ = v___y_2167_;
v___y_2139_ = v___y_2160_;
v___y_2140_ = v___y_2162_;
v___y_2141_ = v___y_2163_;
v___y_2142_ = v___y_2177_;
v___y_2143_ = v___y_2178_;
v___y_2144_ = v___y_2179_;
v___y_2145_ = v___y_2165_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; 
lean_inc_n(v___y_2163_, 3);
v___x_2195_ = lean_task_map(v___f_2105_, v___y_2180_, v___y_2163_, v___x_2102_);
lean_inc_n(v___y_2179_, 3);
lean_inc_n(v___y_2161_, 2);
lean_inc_n(v___y_2166_, 2);
v___x_2196_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2196_, 0, v___y_2166_);
lean_ctor_set(v___x_2196_, 1, v___y_2161_);
lean_ctor_set(v___x_2196_, 2, v___y_2179_);
lean_ctor_set(v___x_2196_, 3, v___x_2195_);
v___x_2197_ = lean_task_map(v___f_2106_, v___y_2159_, v___y_2163_, v___x_2102_);
v___x_2198_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2198_, 0, v___y_2166_);
lean_ctor_set(v___x_2198_, 1, v___y_2161_);
lean_ctor_set(v___x_2198_, 2, v___y_2179_);
lean_ctor_set(v___x_2198_, 3, v___x_2197_);
v___x_2199_ = lean_task_map(v___f_2107_, v___y_2164_, v___y_2163_, v___x_2102_);
v___x_2200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2200_, 0, v___y_2166_);
lean_ctor_set(v___x_2200_, 1, v___y_2161_);
lean_ctor_set(v___x_2200_, 2, v___y_2179_);
lean_ctor_set(v___x_2200_, 3, v___x_2199_);
v___x_2201_ = lean_unsigned_to_nat(3u);
v___x_2202_ = lean_mk_empty_array_with_capacity(v___x_2201_);
v___x_2203_ = lean_array_push(v___x_2202_, v___x_2196_);
v___x_2204_ = lean_array_push(v___x_2203_, v___x_2198_);
v___x_2205_ = lean_array_push(v___x_2204_, v___x_2200_);
v___x_2206_ = l_Array_append___redArg(v___x_2205_, v_snapshotTasks_2173_);
lean_inc_ref(v___y_2165_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2165_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_inc_ref(v___x_2207_);
v___x_2208_ = l_Lean_Language_SnapshotTree_waitAll(v___x_2207_);
v___x_2209_ = lean_box_usize(v___y_2155_);
v___x_2210_ = lean_box(v___x_2102_);
v___x_2211_ = lean_box(v_val_2098_);
v___x_2212_ = lean_box(v___x_2194_);
lean_inc_ref(v_a_2099_);
lean_inc_ref(v___y_2151_);
v___f_2213_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___boxed), 20, 18);
lean_closure_set(v___f_2213_, 0, v___x_2101_);
lean_closure_set(v___f_2213_, 1, v___y_2153_);
lean_closure_set(v___f_2213_, 2, v___y_2158_);
lean_closure_set(v___f_2213_, 3, v___x_2209_);
lean_closure_set(v___f_2213_, 4, v___x_2210_);
lean_closure_set(v___f_2213_, 5, v_env_2168_);
lean_closure_set(v___f_2213_, 6, v___y_2151_);
lean_closure_set(v___f_2213_, 7, v___x_2188_);
lean_closure_set(v___f_2213_, 8, v_a_2099_);
lean_closure_set(v___f_2213_, 9, v_opts_2191_);
lean_closure_set(v___f_2213_, 10, v___x_2207_);
lean_closure_set(v___f_2213_, 11, v_pos_2108_);
lean_closure_set(v___f_2213_, 12, v___x_2211_);
lean_closure_set(v___f_2213_, 13, v___y_2157_);
lean_closure_set(v___f_2213_, 14, v___y_2156_);
lean_closure_set(v___f_2213_, 15, v___y_2152_);
lean_closure_set(v___f_2213_, 16, v___y_2154_);
lean_closure_set(v___f_2213_, 17, v___x_2212_);
v___x_2214_ = lean_io_bind_task(v___x_2208_, v___f_2213_, v___y_2163_, v_val_2098_);
v___y_2119_ = v___y_2167_;
v_snapshotTasks_2120_ = v_snapshotTasks_2173_;
v___y_2121_ = v___y_2160_;
v___y_2122_ = v___y_2162_;
v___y_2123_ = v___y_2178_;
v___y_2124_ = v___y_2177_;
v___y_2125_ = v___y_2179_;
v___y_2126_ = v___y_2165_;
v_traceTask_2127_ = v___x_2214_;
goto v___jp_2118_;
}
}
}
v___jp_2215_:
{
lean_object* v_env_2241_; lean_object* v_messages_2242_; lean_object* v_scopes_2243_; lean_object* v_infoState_2244_; lean_object* v_traceState_2245_; lean_object* v_snapshotTasks_2246_; 
v_env_2241_ = lean_ctor_get(v___y_2232_, 0);
lean_inc_ref(v_env_2241_);
v_messages_2242_ = lean_ctor_get(v___y_2232_, 1);
lean_inc_ref(v_messages_2242_);
v_scopes_2243_ = lean_ctor_get(v___y_2232_, 2);
lean_inc(v_scopes_2243_);
v_infoState_2244_ = lean_ctor_get(v___y_2232_, 8);
lean_inc_ref(v_infoState_2244_);
v_traceState_2245_ = lean_ctor_get(v___y_2232_, 9);
lean_inc_ref(v_traceState_2245_);
v_snapshotTasks_2246_ = lean_ctor_get(v___y_2232_, 10);
lean_inc_ref(v_snapshotTasks_2246_);
v___y_2151_ = v___y_2216_;
v___y_2152_ = v___y_2217_;
v___y_2153_ = v___y_2218_;
v___y_2154_ = v___y_2220_;
v___y_2155_ = v___y_2219_;
v___y_2156_ = v___y_2223_;
v___y_2157_ = v___y_2222_;
v___y_2158_ = v___y_2221_;
v___y_2159_ = v___y_2224_;
v___y_2160_ = v___y_2225_;
v___y_2161_ = v___y_2226_;
v___y_2162_ = v___y_2227_;
v___y_2163_ = v___y_2228_;
v___y_2164_ = v___y_2229_;
v___y_2165_ = v___y_2230_;
v___y_2166_ = v___y_2231_;
v___y_2167_ = v___y_2232_;
v_env_2168_ = v_env_2241_;
v_messages_2169_ = v_messages_2242_;
v_scopes_2170_ = v_scopes_2243_;
v_infoState_2171_ = v_infoState_2244_;
v_traceState_2172_ = v_traceState_2245_;
v_snapshotTasks_2173_ = v_snapshotTasks_2246_;
v___y_2174_ = v___y_2233_;
v___y_2175_ = v___y_2234_;
v___y_2176_ = v___y_2235_;
v___y_2177_ = v___y_2236_;
v___y_2178_ = v___y_2237_;
v___y_2179_ = v___y_2238_;
v___y_2180_ = v___y_2239_;
v_reportedCmdState_2181_ = v_reportedCmdState_2240_;
goto v___jp_2150_;
}
v___jp_2248_:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; uint8_t v___x_2280_; 
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___y_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2114_);
lean_inc_ref(v___y_2258_);
lean_inc_n(v_pos_2108_, 2);
lean_inc_ref(v_cmds_2095_);
lean_inc(v_fst_2096_);
v___x_2276_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab(v_fst_2096_, v_cmds_2095_, v_cmdState_2109_, v_pos_2108_, v___x_2275_, v___y_2258_, v_a_2099_);
v___x_2277_ = lean_box(v_val_2098_);
v___x_2278_ = lean_box(v___x_2102_);
lean_inc_ref(v_a_2099_);
lean_inc(v___y_2255_);
lean_inc_ref(v___x_2104_);
lean_inc_ref(v___x_2276_);
lean_inc_ref(v___y_2249_);
lean_inc_ref(v___y_2256_);
v___f_2279_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__4___boxed), 12, 10);
lean_closure_set(v___f_2279_, 0, v___y_2256_);
lean_closure_set(v___f_2279_, 1, v___y_2249_);
lean_closure_set(v___f_2279_, 2, v___x_2277_);
lean_closure_set(v___f_2279_, 3, v___x_2116_);
lean_closure_set(v___f_2279_, 4, v___x_2276_);
lean_closure_set(v___f_2279_, 5, v___x_2104_);
lean_closure_set(v___f_2279_, 6, v___y_2255_);
lean_closure_set(v___f_2279_, 7, v___x_2278_);
lean_closure_set(v___f_2279_, 8, v_a_2099_);
lean_closure_set(v___f_2279_, 9, v_pos_2108_);
v___x_2280_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2110_, v___x_2247_);
if (v___x_2280_ == 0)
{
lean_dec(v___y_2265_);
lean_inc_ref(v___x_2276_);
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2253_;
v___y_2220_ = v___y_2252_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___y_2254_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2264_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2266_;
v___y_2232_ = v___x_2276_;
v___y_2233_ = v___y_2268_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___f_2279_;
v___y_2236_ = v___y_2270_;
v___y_2237_ = v___y_2269_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2273_;
v_reportedCmdState_2240_ = v___x_2276_;
goto v___jp_2215_;
}
else
{
uint8_t v___x_2281_; uint8_t v___x_2282_; 
lean_inc(v_fst_2096_);
v___x_2281_ = l_Lean_Parser_isTerminalCommand(v_fst_2096_);
v___x_2282_ = lean_bool_not(v___x_2281_);
if (v___x_2282_ == 0)
{
lean_dec(v___y_2265_);
lean_inc_ref(v___x_2276_);
v___y_2216_ = v___y_2249_;
v___y_2217_ = v___y_2250_;
v___y_2218_ = v___y_2251_;
v___y_2219_ = v___y_2253_;
v___y_2220_ = v___y_2252_;
v___y_2221_ = v___y_2255_;
v___y_2222_ = v___y_2256_;
v___y_2223_ = v___y_2254_;
v___y_2224_ = v___y_2257_;
v___y_2225_ = v___y_2258_;
v___y_2226_ = v___y_2259_;
v___y_2227_ = v___y_2260_;
v___y_2228_ = v___y_2261_;
v___y_2229_ = v___y_2264_;
v___y_2230_ = v___y_2263_;
v___y_2231_ = v___y_2266_;
v___y_2232_ = v___x_2276_;
v___y_2233_ = v___y_2268_;
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___f_2279_;
v___y_2236_ = v___y_2270_;
v___y_2237_ = v___y_2269_;
v___y_2238_ = v___y_2271_;
v___y_2239_ = v___y_2273_;
v_reportedCmdState_2240_ = v___x_2276_;
goto v___jp_2215_;
}
else
{
lean_object* v_env_2283_; lean_object* v_messages_2284_; lean_object* v_scopes_2285_; lean_object* v_infoState_2286_; lean_object* v_traceState_2287_; lean_object* v_snapshotTasks_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_env_2283_ = lean_ctor_get(v___x_2276_, 0);
lean_inc_ref_n(v_env_2283_, 2);
v_messages_2284_ = lean_ctor_get(v___x_2276_, 1);
lean_inc_ref(v_messages_2284_);
v_scopes_2285_ = lean_ctor_get(v___x_2276_, 2);
lean_inc(v_scopes_2285_);
v_infoState_2286_ = lean_ctor_get(v___x_2276_, 8);
lean_inc_ref(v_infoState_2286_);
v_traceState_2287_ = lean_ctor_get(v___x_2276_, 9);
lean_inc_ref(v_traceState_2287_);
v_snapshotTasks_2288_ = lean_ctor_get(v___x_2276_, 10);
lean_inc_ref(v_snapshotTasks_2288_);
v___x_2289_ = lean_mk_empty_array_with_capacity(v___y_2265_);
lean_dec(v___y_2265_);
lean_inc_ref(v___x_2289_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
lean_inc_n(v___y_2261_, 3);
v___x_2291_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v___x_2289_);
lean_ctor_set(v___x_2291_, 2, v___y_2261_);
lean_ctor_set(v___x_2291_, 3, v___y_2261_);
lean_ctor_set_usize(v___x_2291_, 4, v___y_2262_);
v___x_2292_ = l_Lean_NameSet_empty;
lean_inc_ref_n(v___x_2291_, 2);
v___x_2293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2291_);
lean_ctor_set(v___x_2293_, 2, v___x_2292_);
v___x_2294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2295_ = l_Lean_Options_empty;
v___x_2296_ = lean_box(0);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___y_2261_);
lean_inc_ref_n(v___x_2297_, 2);
lean_inc_n(v___x_2101_, 2);
v___x_2298_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v___x_2298_, 0, v___x_2294_);
lean_ctor_set(v___x_2298_, 1, v___x_2295_);
lean_ctor_set(v___x_2298_, 2, v___x_2101_);
lean_ctor_set(v___x_2298_, 3, v___x_2296_);
lean_ctor_set(v___x_2298_, 4, v___x_2296_);
lean_ctor_set(v___x_2298_, 5, v___x_2297_);
lean_ctor_set(v___x_2298_, 6, v___x_2297_);
lean_ctor_set(v___x_2298_, 7, v___x_2296_);
lean_ctor_set(v___x_2298_, 8, v___x_2296_);
lean_ctor_set(v___x_2298_, 9, v___x_2296_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*10, v_val_2098_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*10 + 1, v_val_2098_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*10 + 2, v_val_2098_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2296_);
v___x_2300_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__0);
v___x_2301_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__3___closed__3));
v___x_2302_ = l_Lean_DeclNameGenerator_ofPrefix(v___x_2101_);
v___x_2303_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__4);
v___x_2304_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
lean_ctor_set(v___x_2304_, 2, v___x_2291_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*3, v___x_2102_);
lean_inc_ref(v___y_2272_);
v___x_2305_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2305_, 0, v_env_2283_);
lean_ctor_set(v___x_2305_, 1, v___x_2293_);
lean_ctor_set(v___x_2305_, 2, v___x_2299_);
lean_ctor_set(v___x_2305_, 3, v___x_2292_);
lean_ctor_set(v___x_2305_, 4, v___x_2300_);
lean_ctor_set(v___x_2305_, 5, v___y_2261_);
lean_ctor_set(v___x_2305_, 6, v___x_2301_);
lean_ctor_set(v___x_2305_, 7, v___x_2302_);
lean_ctor_set(v___x_2305_, 8, v___x_2304_);
lean_ctor_set(v___x_2305_, 9, v___y_2272_);
lean_ctor_set(v___x_2305_, 10, v___x_2297_);
v___y_2151_ = v___y_2249_;
v___y_2152_ = v___y_2250_;
v___y_2153_ = v___y_2251_;
v___y_2154_ = v___y_2252_;
v___y_2155_ = v___y_2253_;
v___y_2156_ = v___y_2254_;
v___y_2157_ = v___y_2256_;
v___y_2158_ = v___y_2255_;
v___y_2159_ = v___y_2257_;
v___y_2160_ = v___y_2258_;
v___y_2161_ = v___y_2259_;
v___y_2162_ = v___y_2260_;
v___y_2163_ = v___y_2261_;
v___y_2164_ = v___y_2264_;
v___y_2165_ = v___y_2263_;
v___y_2166_ = v___y_2266_;
v___y_2167_ = v___x_2276_;
v_env_2168_ = v_env_2283_;
v_messages_2169_ = v_messages_2284_;
v_scopes_2170_ = v_scopes_2285_;
v_infoState_2171_ = v_infoState_2286_;
v_traceState_2172_ = v_traceState_2287_;
v_snapshotTasks_2173_ = v_snapshotTasks_2288_;
v___y_2174_ = v___y_2268_;
v___y_2175_ = v___y_2267_;
v___y_2176_ = v___f_2279_;
v___y_2177_ = v___y_2270_;
v___y_2178_ = v___y_2269_;
v___y_2179_ = v___y_2271_;
v___y_2180_ = v___y_2273_;
v_reportedCmdState_2181_ = v___x_2305_;
goto v___jp_2150_;
}
}
}
v___jp_2306_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; size_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2312_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_2100_);
v___x_2313_ = l_IO_CancelToken_new();
v___x_2314_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
lean_inc(v___x_2101_);
v___x_2315_ = l_Lean_Name_str___override(v___x_2101_, v___x_2314_);
v___x_2316_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2317_ = l_Lean_Name_str___override(v___x_2315_, v___x_2316_);
v___x_2318_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2319_ = l_Lean_Name_str___override(v___x_2317_, v___x_2318_);
v___x_2320_ = l_Lean_Name_str___override(v___x_2319_, v___x_2316_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = l_Lean_Name_num___override(v___x_2320_, v___x_2321_);
v___x_2323_ = l_Lean_Name_str___override(v___x_2322_, v___x_2316_);
v___x_2324_ = l_Lean_Name_str___override(v___x_2323_, v___x_2318_);
v___x_2325_ = l_Lean_Name_str___override(v___x_2324_, v___x_2316_);
v___x_2326_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2327_ = l_Lean_Name_str___override(v___x_2325_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2329_ = l_Lean_Name_str___override(v___x_2327_, v___x_2328_);
v___x_2330_ = l_Lean_Name_toString(v___x_2329_, v___x_2102_);
v___x_2331_ = lean_box(0);
v___x_2332_ = lean_unsigned_to_nat(32u);
v___x_2333_ = lean_mk_empty_array_with_capacity(v___x_2332_);
lean_dec_ref(v___x_2333_);
v___x_2334_ = ((size_t)5ULL);
v___x_2335_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
lean_inc_ref_n(v___x_2330_, 2);
v___x_2336_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2336_, 0, v___x_2330_);
lean_ctor_set(v___x_2336_, 1, v___x_2312_);
lean_ctor_set(v___x_2336_, 2, v___x_2331_);
lean_ctor_set(v___x_2336_, 3, v___x_2335_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*4, v_val_2098_);
v___x_2337_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2338_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2338_, 0, v___x_2330_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
lean_ctor_set(v___x_2338_, 2, v___x_2331_);
lean_ctor_set(v___x_2338_, 3, v___x_2335_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*4, v_val_2098_);
lean_inc(v___y_2309_);
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___y_2309_);
v___x_2340_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2339_);
lean_inc_ref(v___x_2313_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2313_);
v___x_2342_ = l_IO_Promise_result_x21___redArg(v___x_2114_);
lean_inc_ref(v___x_2342_);
lean_inc(v___x_2340_);
lean_inc_ref_n(v___x_2339_, 3);
v___x_2343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2339_);
lean_ctor_set(v___x_2343_, 1, v___x_2340_);
lean_ctor_set(v___x_2343_, 2, v___x_2341_);
lean_ctor_set(v___x_2343_, 3, v___x_2342_);
v___x_2344_ = l_IO_Promise_result_x21___redArg(v___x_2115_);
lean_inc_ref(v___x_2344_);
lean_inc_n(v___y_2307_, 3);
v___x_2345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2339_);
lean_ctor_set(v___x_2345_, 1, v___y_2307_);
lean_ctor_set(v___x_2345_, 2, v___x_2331_);
lean_ctor_set(v___x_2345_, 3, v___x_2344_);
v___x_2346_ = l_IO_Promise_result_x21___redArg(v___x_2116_);
lean_inc_ref(v___x_2346_);
v___x_2347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2339_);
lean_ctor_set(v___x_2347_, 1, v___y_2307_);
lean_ctor_set(v___x_2347_, 2, v___x_2331_);
lean_ctor_set(v___x_2347_, 3, v___x_2346_);
v___x_2348_ = l_IO_Promise_result_x21___redArg(v___x_2117_);
v___x_2349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2331_);
lean_ctor_set(v___x_2349_, 1, v___y_2307_);
lean_ctor_set(v___x_2349_, 2, v___x_2331_);
lean_ctor_set(v___x_2349_, 3, v___x_2348_);
lean_inc_ref(v___x_2338_);
v___x_2350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2338_);
lean_ctor_set(v___x_2350_, 1, v___x_2343_);
lean_ctor_set(v___x_2350_, 2, v___x_2345_);
lean_ctor_set(v___x_2350_, 3, v___x_2347_);
lean_ctor_set(v___x_2350_, 4, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2336_);
lean_ctor_set(v___x_2351_, 1, v___y_2309_);
lean_ctor_set(v___x_2351_, 2, v___y_2310_);
lean_ctor_set(v___x_2351_, 3, v___x_2350_);
lean_ctor_set(v___x_2351_, 4, v___y_2311_);
v___x_2352_ = lean_io_promise_resolve(v___x_2351_, v_prom_2103_);
if (lean_obj_tag(v_old_x3f_2111_) == 0)
{
lean_inc_ref(v___x_2330_);
lean_inc_ref(v___x_2338_);
v___y_2249_ = v___x_2335_;
v___y_2250_ = v___x_2338_;
v___y_2251_ = v___x_2332_;
v___y_2252_ = v___x_2331_;
v___y_2253_ = v___x_2334_;
v___y_2254_ = v___x_2331_;
v___y_2255_ = v___x_2321_;
v___y_2256_ = v___x_2330_;
v___y_2257_ = v___x_2344_;
v___y_2258_ = v___x_2313_;
v___y_2259_ = v___x_2340_;
v___y_2260_ = v___y_2307_;
v___y_2261_ = v___x_2321_;
v___y_2262_ = v___x_2334_;
v___y_2263_ = v___x_2338_;
v___y_2264_ = v___x_2346_;
v___y_2265_ = v___x_2332_;
v___y_2266_ = v___x_2339_;
v___y_2267_ = v___x_2331_;
v___y_2268_ = v___x_2330_;
v___y_2269_ = v___y_2308_;
v___y_2270_ = v___x_2331_;
v___y_2271_ = v___x_2331_;
v___y_2272_ = v___x_2335_;
v___y_2273_ = v___x_2342_;
v___y_2274_ = v___x_2331_;
goto v___jp_2248_;
}
else
{
lean_object* v_val_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2364_; 
v_val_2353_ = lean_ctor_get(v_old_x3f_2111_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_old_x3f_2111_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2355_ = v_old_x3f_2111_;
v_isShared_2356_ = v_isSharedCheck_2364_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_val_2353_);
lean_dec(v_old_x3f_2111_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2364_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_elabSnap_2357_; lean_object* v_stx_2358_; lean_object* v_elabSnap_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
v_elabSnap_2357_ = lean_ctor_get(v_val_2353_, 3);
lean_inc_ref(v_elabSnap_2357_);
v_stx_2358_ = lean_ctor_get(v_val_2353_, 1);
lean_inc(v_stx_2358_);
lean_dec(v_val_2353_);
v_elabSnap_2359_ = lean_ctor_get(v_elabSnap_2357_, 1);
lean_inc_ref(v_elabSnap_2359_);
lean_dec_ref(v_elabSnap_2357_);
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_stx_2358_);
lean_ctor_set(v___x_2360_, 1, v_elabSnap_2359_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2360_);
v___x_2362_ = v___x_2355_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_inc_ref(v___x_2330_);
lean_inc_ref(v___x_2338_);
v___y_2249_ = v___x_2335_;
v___y_2250_ = v___x_2338_;
v___y_2251_ = v___x_2332_;
v___y_2252_ = v___x_2331_;
v___y_2253_ = v___x_2334_;
v___y_2254_ = v___x_2331_;
v___y_2255_ = v___x_2321_;
v___y_2256_ = v___x_2330_;
v___y_2257_ = v___x_2344_;
v___y_2258_ = v___x_2313_;
v___y_2259_ = v___x_2340_;
v___y_2260_ = v___y_2307_;
v___y_2261_ = v___x_2321_;
v___y_2262_ = v___x_2334_;
v___y_2263_ = v___x_2338_;
v___y_2264_ = v___x_2346_;
v___y_2265_ = v___x_2332_;
v___y_2266_ = v___x_2339_;
v___y_2267_ = v___x_2331_;
v___y_2268_ = v___x_2330_;
v___y_2269_ = v___y_2308_;
v___y_2270_ = v___x_2331_;
v___y_2271_ = v___x_2331_;
v___y_2272_ = v___x_2335_;
v___y_2273_ = v___x_2342_;
v___y_2274_ = v___x_2362_;
goto v___jp_2248_;
}
}
}
}
v___jp_2365_:
{
lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2369_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2368_);
lean_inc(v_fst_2096_);
v___x_2370_ = l_Lean_Parser_isTerminalCommand(v_fst_2096_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v_toProcessingContext_2372_; lean_object* v_pos_2373_; lean_object* v_endPos_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2371_ = lean_io_promise_new();
v_toProcessingContext_2372_ = lean_ctor_get(v_a_2099_, 0);
v_pos_2373_ = lean_ctor_get(v_fst_2097_, 0);
v_endPos_2374_ = lean_ctor_get(v_toProcessingContext_2372_, 3);
lean_inc(v___x_2371_);
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2371_);
v___x_2376_ = lean_box(0);
lean_inc(v_endPos_2374_);
lean_inc(v_pos_2373_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_pos_2373_);
lean_ctor_set(v___x_2377_, 1, v_endPos_2374_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v_parseCancelTk_2112_);
v___x_2380_ = l_IO_Promise_result_x21___redArg(v___x_2371_);
lean_dec(v___x_2371_);
v___x_2381_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2376_);
lean_ctor_set(v___x_2381_, 1, v___x_2378_);
lean_ctor_set(v___x_2381_, 2, v___x_2379_);
lean_ctor_set(v___x_2381_, 3, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
v___y_2307_ = v___x_2369_;
v___y_2308_ = v___x_2375_;
v___y_2309_ = v___y_2366_;
v___y_2310_ = v___y_2367_;
v___y_2311_ = v___x_2382_;
goto v___jp_2306_;
}
else
{
lean_object* v___x_2383_; 
lean_dec_ref(v_parseCancelTk_2112_);
v___x_2383_ = lean_box(0);
v___y_2307_ = v___x_2369_;
v___y_2308_ = v___x_2383_;
v___y_2309_ = v___y_2366_;
v___y_2310_ = v___y_2367_;
v___y_2311_ = v___x_2383_;
goto v___jp_2306_;
}
}
v___jp_2384_:
{
lean_object* v___x_2387_; 
lean_inc(v_fst_2096_);
v___x_2387_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v_fst_2096_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_box(0);
v___y_2366_ = v_fst_2385_;
v___y_2367_ = v_snd_2386_;
v___y_2368_ = v___x_2388_;
goto v___jp_2365_;
}
else
{
lean_object* v_val_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2397_; 
v_val_2389_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_val_2389_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2397_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
lean_inc(v_val_2389_);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v_val_2389_);
lean_ctor_set(v___x_2393_, 1, v_val_2389_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2393_);
v___x_2395_ = v___x_2391_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
v___y_2366_ = v_fst_2385_;
v___y_2367_ = v_snd_2386_;
v___y_2368_ = v___x_2395_;
goto v___jp_2365_;
}
}
}
}
v___jp_2398_:
{
if (v___y_2399_ == 0)
{
lean_inc_ref(v_fst_2097_);
lean_inc(v_fst_2096_);
v_fst_2385_ = v_fst_2096_;
v_snd_2386_ = v_fst_2097_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_box(0);
v___x_2401_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_fst_2385_ = v___x_2400_;
v_snd_2386_ = v___x_2401_;
goto v___jp_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed(lean_object** _args){
lean_object* v_cmds_2405_ = _args[0];
lean_object* v_fst_2406_ = _args[1];
lean_object* v_fst_2407_ = _args[2];
lean_object* v_val_2408_ = _args[3];
lean_object* v_a_2409_ = _args[4];
lean_object* v_snd_2410_ = _args[5];
lean_object* v___x_2411_ = _args[6];
lean_object* v___x_2412_ = _args[7];
lean_object* v_prom_2413_ = _args[8];
lean_object* v___x_2414_ = _args[9];
lean_object* v___f_2415_ = _args[10];
lean_object* v___f_2416_ = _args[11];
lean_object* v___f_2417_ = _args[12];
lean_object* v_pos_2418_ = _args[13];
lean_object* v_cmdState_2419_ = _args[14];
lean_object* v_opts_2420_ = _args[15];
lean_object* v_old_x3f_2421_ = _args[16];
lean_object* v_parseCancelTk_2422_ = _args[17];
lean_object* v___y_2423_ = _args[18];
_start:
{
uint8_t v_val_45553__boxed_2424_; uint8_t v___x_45556__boxed_2425_; lean_object* v_res_2426_; 
v_val_45553__boxed_2424_ = lean_unbox(v_val_2408_);
v___x_45556__boxed_2425_ = lean_unbox(v___x_2412_);
v_res_2426_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8(v_cmds_2405_, v_fst_2406_, v_fst_2407_, v_val_45553__boxed_2424_, v_a_2409_, v_snd_2410_, v___x_2411_, v___x_45556__boxed_2425_, v_prom_2413_, v___x_2414_, v___f_2415_, v___f_2416_, v___f_2417_, v_pos_2418_, v_cmdState_2419_, v_opts_2420_, v_old_x3f_2421_, v_parseCancelTk_2422_);
lean_dec_ref(v_opts_2420_);
lean_dec(v_prom_2413_);
lean_dec_ref(v_a_2409_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(lean_object* v_old_x3f_2429_, lean_object* v_parserState_2430_, lean_object* v_cmdState_2431_, lean_object* v_prom_2432_, uint8_t v_sync_2433_, lean_object* v_parseCancelTk_2434_, lean_object* v_cmds_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_toSnapshot_2439_; lean_object* v_stx_2440_; lean_object* v_parserState_2441_; lean_object* v_elabSnap_2442_; lean_object* v_val_2443_; lean_object* v_newParserState_2444_; lean_object* v___y_2478_; lean_object* v___y_2480_; lean_object* v___y_2481_; uint8_t v___y_2482_; lean_object* v___y_2516_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___f_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; uint8_t v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2558_; uint8_t v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; uint8_t v___y_2586_; uint8_t v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; 
v___f_2520_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__2));
v___f_2521_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__3));
v___f_2522_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__4));
v___x_2523_ = l_Lean_Elab_Command_instInhabitedScope_default;
if (lean_obj_tag(v_old_x3f_2429_) == 1)
{
lean_object* v_val_2669_; lean_object* v_nextCmdSnap_x3f_2670_; 
v_val_2669_ = lean_ctor_get(v_old_x3f_2429_, 0);
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
v___x_2684_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_2683_, v_a_2436_);
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
lean_dec_ref_known(v_old_x3f_2429_, 1);
lean_dec_ref(v_parseCancelTk_2434_);
lean_dec_ref(v_cmdState_2431_);
lean_dec_ref(v_parserState_2430_);
v_toSnapshot_2439_ = v_toSnapshot_2671_;
v_stx_2440_ = v_stx_2672_;
v_parserState_2441_ = v_parserState_2673_;
v_elabSnap_2442_ = v_elabSnap_2674_;
v_val_2443_ = v_val_2675_;
v_newParserState_2444_ = v_parserState_2673_;
goto v___jp_2438_;
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
v___jp_2438_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_resultSnap_2447_; lean_object* v_task_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2471_; 
v___x_2445_ = lean_io_promise_new();
v___x_2446_ = l_IO_CancelToken_new();
v_resultSnap_2447_ = lean_ctor_get(v_elabSnap_2442_, 2);
lean_inc_ref(v_resultSnap_2447_);
v_task_2448_ = lean_ctor_get(v_resultSnap_2447_, 3);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_resultSnap_2447_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; lean_object* v_unused_2473_; lean_object* v_unused_2474_; 
v_unused_2472_ = lean_ctor_get(v_resultSnap_2447_, 2);
lean_dec(v_unused_2472_);
v_unused_2473_ = lean_ctor_get(v_resultSnap_2447_, 1);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_resultSnap_2447_, 0);
lean_dec(v_unused_2474_);
v___x_2450_ = v_resultSnap_2447_;
v_isShared_2451_ = v_isSharedCheck_2471_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_task_2448_);
lean_dec(v_resultSnap_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2471_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___x_2456_; lean_object* v_toProcessingContext_2457_; lean_object* v_pos_2458_; lean_object* v_endPos_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2452_ = lean_box(v_sync_2433_);
lean_inc_ref(v_a_2436_);
lean_inc_ref(v___x_2446_);
lean_inc(v___x_2445_);
lean_inc_ref(v_newParserState_2444_);
lean_inc(v_stx_2440_);
v___f_2453_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__1___boxed), 10, 8);
lean_closure_set(v___f_2453_, 0, v_val_2443_);
lean_closure_set(v___f_2453_, 1, v_cmds_2435_);
lean_closure_set(v___f_2453_, 2, v_stx_2440_);
lean_closure_set(v___f_2453_, 3, v_newParserState_2444_);
lean_closure_set(v___f_2453_, 4, v___x_2445_);
lean_closure_set(v___f_2453_, 5, v___x_2452_);
lean_closure_set(v___f_2453_, 6, v___x_2446_);
lean_closure_set(v___f_2453_, 7, v_a_2436_);
v___x_2454_ = lean_unsigned_to_nat(0u);
v___x_2455_ = 1;
v___x_2456_ = l_BaseIO_chainTask___redArg(v_task_2448_, v___f_2453_, v___x_2454_, v___x_2455_);
v_toProcessingContext_2457_ = lean_ctor_get(v_a_2436_, 0);
v_pos_2458_ = lean_ctor_get(v_newParserState_2444_, 0);
lean_inc(v_pos_2458_);
lean_dec_ref(v_newParserState_2444_);
v_endPos_2459_ = lean_ctor_get(v_toProcessingContext_2457_, 3);
v___x_2460_ = lean_box(0);
lean_inc(v_endPos_2459_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_pos_2458_);
lean_ctor_set(v___x_2461_, 1, v_endPos_2459_);
v___x_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
v___x_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2446_);
v___x_2464_ = l_IO_Promise_result_x21___redArg(v___x_2445_);
lean_dec(v___x_2445_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 3, v___x_2464_);
lean_ctor_set(v___x_2450_, 2, v___x_2463_);
lean_ctor_set(v___x_2450_, 1, v___x_2462_);
lean_ctor_set(v___x_2450_, 0, v___x_2460_);
v___x_2466_ = v___x_2450_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2468_, 0, v_toSnapshot_2439_);
lean_ctor_set(v___x_2468_, 1, v_stx_2440_);
lean_ctor_set(v___x_2468_, 2, v_parserState_2441_);
lean_ctor_set(v___x_2468_, 3, v_elabSnap_2442_);
lean_ctor_set(v___x_2468_, 4, v___x_2467_);
v___x_2469_ = lean_io_promise_resolve(v___x_2468_, v_prom_2432_);
lean_dec(v_prom_2432_);
return v___x_2469_;
}
}
}
v___jp_2475_:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
v___jp_2477_:
{
goto v___jp_2475_;
}
v___jp_2479_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2483_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__0));
v___x_2484_ = l_Lean_Name_str___override(v___y_2481_, v___x_2483_);
v___x_2485_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2486_ = l_Lean_Name_str___override(v___x_2484_, v___x_2485_);
v___x_2487_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2488_ = l_Lean_Name_str___override(v___x_2486_, v___x_2487_);
v___x_2489_ = l_Lean_Name_str___override(v___x_2488_, v___x_2485_);
v___x_2490_ = lean_unsigned_to_nat(0u);
v___x_2491_ = l_Lean_Name_num___override(v___x_2489_, v___x_2490_);
v___x_2492_ = l_Lean_Name_str___override(v___x_2491_, v___x_2485_);
v___x_2493_ = l_Lean_Name_str___override(v___x_2492_, v___x_2487_);
v___x_2494_ = l_Lean_Name_str___override(v___x_2493_, v___x_2485_);
v___x_2495_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2496_ = l_Lean_Name_str___override(v___x_2494_, v___x_2495_);
v___x_2497_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5___closed__5));
v___x_2498_ = l_Lean_Name_str___override(v___x_2496_, v___x_2497_);
v___x_2499_ = l_Lean_Name_toString(v___x_2498_, v___y_2482_);
v___x_2500_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_2503_ = 0;
v___x_2504_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2504_, 0, v___x_2499_);
lean_ctor_set(v___x_2504_, 1, v___x_2500_);
lean_ctor_set(v___x_2504_, 2, v___x_2501_);
lean_ctor_set(v___x_2504_, 3, v___x_2502_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*4, v___x_2503_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
lean_inc_ref_n(v___x_2504_, 3);
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2504_);
lean_ctor_set(v___x_2507_, 1, v_cmdState_2431_);
v___x_2508_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2501_, v___x_2507_);
v___x_2509_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_2501_, v___x_2504_);
v___x_2510_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v___x_2511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2504_);
lean_ctor_set(v___x_2511_, 1, v___x_2506_);
lean_ctor_set(v___x_2511_, 2, v___x_2508_);
lean_ctor_set(v___x_2511_, 3, v___x_2509_);
lean_ctor_set(v___x_2511_, 4, v___x_2510_);
v___x_2512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2504_);
lean_ctor_set(v___x_2512_, 1, v___x_2505_);
lean_ctor_set(v___x_2512_, 2, v___y_2480_);
lean_ctor_set(v___x_2512_, 3, v___x_2511_);
lean_ctor_set(v___x_2512_, 4, v___x_2501_);
v___x_2513_ = lean_io_promise_resolve(v___x_2512_, v_prom_2432_);
lean_dec(v_prom_2432_);
v___x_2514_ = lean_box(0);
return v___x_2514_;
}
v___jp_2515_:
{
v___y_2480_ = v___y_2516_;
v___y_2481_ = v___y_2517_;
v___y_2482_ = v___y_2518_;
goto v___jp_2479_;
}
v___jp_2524_:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(v___y_2541_);
v___x_2543_ = l_Lean_Parser_isTerminalCommand(v___y_2535_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_io_promise_new();
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
v___x_2546_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2542_, v___y_2529_, v_cmds_2435_, v___y_2537_, v___y_2532_, v___y_2534_, v_a_2436_, v___y_2538_, v___y_2525_, v___y_2536_, v___y_2539_, v___y_2527_, v___y_2530_, v___y_2528_, v___y_2533_, v_prom_2432_, v___x_2523_, v___f_2520_, v___f_2521_, v___f_2522_, v___y_2531_, v_cmdState_2431_, v___y_2540_, v___y_2526_, v_old_x3f_2429_, v_parseCancelTk_2434_, v___x_2545_);
lean_dec_ref(v___y_2540_);
lean_dec(v_prom_2432_);
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
v___y_2478_ = v___x_2546_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2542_, v___y_2529_, v_cmds_2435_, v___y_2537_, v___y_2532_, v___y_2534_, v_a_2436_, v___y_2538_, v___y_2525_, v___y_2536_, v___y_2539_, v___y_2527_, v___y_2530_, v___y_2528_, v___y_2533_, v_prom_2432_, v___x_2523_, v___f_2520_, v___f_2521_, v___f_2522_, v___y_2531_, v_cmdState_2431_, v___y_2540_, v___y_2526_, v_old_x3f_2429_, v_parseCancelTk_2434_, v___x_2547_);
lean_dec_ref(v___y_2540_);
lean_dec(v_prom_2432_);
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
v___y_2478_ = v___x_2548_;
goto v___jp_2477_;
}
}
v___jp_2549_:
{
lean_object* v___x_2566_; 
lean_inc(v___y_2563_);
v___x_2566_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_getNiceCommandStartPos_x3f(v___y_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_box(0);
v___y_2525_ = v___y_2550_;
v___y_2526_ = v___y_2551_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v___y_2556_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v_snd_2565_;
v___y_2534_ = v___y_2558_;
v___y_2535_ = v___y_2563_;
v___y_2536_ = v___y_2559_;
v___y_2537_ = v___y_2560_;
v___y_2538_ = v___y_2561_;
v___y_2539_ = v_fst_2564_;
v___y_2540_ = v___y_2562_;
v___y_2541_ = v___x_2567_;
goto v___jp_2524_;
}
else
{
lean_object* v_val_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2576_; 
v_val_2568_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2570_ = v___x_2566_;
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_val_2568_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2576_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_inc(v_val_2568_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_val_2568_);
lean_ctor_set(v___x_2572_, 1, v_val_2568_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2572_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
v___y_2525_ = v___y_2550_;
v___y_2526_ = v___y_2551_;
v___y_2527_ = v___y_2552_;
v___y_2528_ = v___y_2553_;
v___y_2529_ = v___y_2554_;
v___y_2530_ = v___y_2555_;
v___y_2531_ = v___y_2556_;
v___y_2532_ = v___y_2557_;
v___y_2533_ = v_snd_2565_;
v___y_2534_ = v___y_2558_;
v___y_2535_ = v___y_2563_;
v___y_2536_ = v___y_2559_;
v___y_2537_ = v___y_2560_;
v___y_2538_ = v___y_2561_;
v___y_2539_ = v_fst_2564_;
v___y_2540_ = v___y_2562_;
v___y_2541_ = v___x_2574_;
goto v___jp_2524_;
}
}
}
}
v___jp_2577_:
{
if (v___y_2593_ == 0)
{
lean_inc(v___y_2592_);
v___y_2550_ = v___y_2578_;
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
v___y_2563_ = v___y_2592_;
v_fst_2564_ = v___y_2592_;
v_snd_2565_ = v___y_2591_;
goto v___jp_2549_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec_ref(v___y_2591_);
v___x_2594_ = lean_box(0);
v___x_2595_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v___y_2550_ = v___y_2578_;
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
v___y_2563_ = v___y_2592_;
v_fst_2564_ = v___x_2594_;
v_snd_2565_ = v___x_2595_;
goto v___jp_2549_;
}
}
v___jp_2596_:
{
uint8_t v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = l_IO_CancelToken_isSet(v_parseCancelTk_2434_);
v___x_2608_ = 1;
if (v___x_2607_ == 0)
{
lean_dec(v___y_2604_);
if (v_sync_2433_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2609_ = lean_io_promise_new();
v___x_2610_ = lean_io_promise_new();
v___x_2611_ = lean_io_promise_new();
v___x_2612_ = lean_io_promise_new();
v___x_2613_ = l_Lean_internal_cmdlineSnapshots;
v___x_2614_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v___y_2606_, v___x_2613_);
lean_dec_ref(v___y_2606_);
if (v___x_2614_ == 0)
{
v___y_2578_ = v___y_2598_;
v___y_2579_ = v___x_2613_;
v___y_2580_ = v___x_2609_;
v___y_2581_ = v___x_2611_;
v___y_2582_ = v___x_2612_;
v___y_2583_ = v___x_2610_;
v___y_2584_ = v___y_2602_;
v___y_2585_ = v___y_2597_;
v___y_2586_ = v___x_2607_;
v___y_2587_ = v___x_2608_;
v___y_2588_ = v___y_2599_;
v___y_2589_ = v___y_2600_;
v___y_2590_ = v___y_2601_;
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2605_;
v___y_2593_ = v___x_2614_;
goto v___jp_2577_;
}
else
{
uint8_t v___x_2615_; uint8_t v___x_2616_; 
lean_inc(v___y_2605_);
v___x_2615_ = l_Lean_Parser_isTerminalCommand(v___y_2605_);
v___x_2616_ = lean_bool_not(v___x_2615_);
v___y_2578_ = v___y_2598_;
v___y_2579_ = v___x_2613_;
v___y_2580_ = v___x_2609_;
v___y_2581_ = v___x_2611_;
v___y_2582_ = v___x_2612_;
v___y_2583_ = v___x_2610_;
v___y_2584_ = v___y_2602_;
v___y_2585_ = v___y_2597_;
v___y_2586_ = v___x_2607_;
v___y_2587_ = v___x_2608_;
v___y_2588_ = v___y_2599_;
v___y_2589_ = v___y_2600_;
v___y_2590_ = v___y_2601_;
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2605_;
v___y_2593_ = v___x_2616_;
goto v___jp_2577_;
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2603_);
v___x_2617_ = lean_box(v___x_2607_);
v___x_2618_ = lean_box(v___x_2608_);
lean_inc_ref(v_a_2436_);
v___f_2619_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__8___boxed), 19, 18);
lean_closure_set(v___f_2619_, 0, v_cmds_2435_);
lean_closure_set(v___f_2619_, 1, v___y_2599_);
lean_closure_set(v___f_2619_, 2, v___y_2597_);
lean_closure_set(v___f_2619_, 3, v___x_2617_);
lean_closure_set(v___f_2619_, 4, v_a_2436_);
lean_closure_set(v___f_2619_, 5, v___y_2600_);
lean_closure_set(v___f_2619_, 6, v___y_2598_);
lean_closure_set(v___f_2619_, 7, v___x_2618_);
lean_closure_set(v___f_2619_, 8, v_prom_2432_);
lean_closure_set(v___f_2619_, 9, v___x_2523_);
lean_closure_set(v___f_2619_, 10, v___f_2520_);
lean_closure_set(v___f_2619_, 11, v___f_2521_);
lean_closure_set(v___f_2619_, 12, v___f_2522_);
lean_closure_set(v___f_2619_, 13, v___y_2602_);
lean_closure_set(v___f_2619_, 14, v_cmdState_2431_);
lean_closure_set(v___f_2619_, 15, v___y_2601_);
lean_closure_set(v___f_2619_, 16, v_old_x3f_2429_);
lean_closure_set(v___f_2619_, 17, v_parseCancelTk_2434_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_io_as_task(v___f_2619_, v___x_2620_);
lean_dec_ref(v___x_2621_);
goto v___jp_2475_;
}
}
else
{
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_cmds_2435_);
lean_dec_ref(v_parseCancelTk_2434_);
if (lean_obj_tag(v_old_x3f_2429_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; lean_object* v_children_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v_val_2622_ = lean_ctor_get(v_old_x3f_2429_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v_old_x3f_2429_, 1);
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
v___y_2480_ = v___y_2603_;
v___y_2481_ = v___y_2604_;
v___y_2482_ = v___x_2608_;
goto v___jp_2479_;
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
v___y_2480_ = v___y_2603_;
v___y_2481_ = v___y_2604_;
v___y_2482_ = v___x_2608_;
goto v___jp_2479_;
}
else
{
size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((size_t)0ULL);
v___x_2631_ = lean_usize_of_nat(v___x_2626_);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2624_, v___x_2630_, v___x_2631_, v___x_2628_);
lean_dec_ref(v_children_2624_);
v___y_2516_ = v___y_2603_;
v___y_2517_ = v___y_2604_;
v___y_2518_ = v___x_2608_;
v___y_2519_ = v___x_2632_;
goto v___jp_2515_;
}
}
else
{
size_t v___x_2633_; size_t v___x_2634_; lean_object* v___x_2635_; 
v___x_2633_ = ((size_t)0ULL);
v___x_2634_ = lean_usize_of_nat(v___x_2626_);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd_spec__6___redArg(v_children_2624_, v___x_2633_, v___x_2634_, v___x_2628_);
lean_dec_ref(v_children_2624_);
v___y_2516_ = v___y_2603_;
v___y_2517_ = v___y_2604_;
v___y_2518_ = v___x_2608_;
v___y_2519_ = v___x_2635_;
goto v___jp_2515_;
}
}
}
else
{
lean_dec(v_old_x3f_2429_);
v___y_2480_ = v___y_2603_;
v___y_2481_ = v___y_2604_;
v___y_2482_ = v___x_2608_;
goto v___jp_2479_;
}
}
}
v___jp_2636_:
{
lean_object* v_env_2637_; lean_object* v_scopes_2638_; lean_object* v___x_2639_; lean_object* v_opts_2640_; lean_object* v_currNamespace_2641_; lean_object* v_openDecls_2642_; lean_object* v___x_2643_; lean_object* v___f_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v_snd_2648_; 
v_env_2637_ = lean_ctor_get(v_cmdState_2431_, 0);
v_scopes_2638_ = lean_ctor_get(v_cmdState_2431_, 2);
v___x_2639_ = l_List_head_x21___redArg(v___x_2523_, v_scopes_2638_);
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
lean_inc_ref(v_parserState_2430_);
lean_inc_ref(v_a_2436_);
v___f_2644_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2644_, 0, v_a_2436_);
lean_closure_set(v___f_2644_, 1, v___x_2643_);
lean_closure_set(v___f_2644_, 2, v_parserState_2430_);
v___x_2645_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__5));
v___x_2646_ = lean_box(0);
v___x_2647_ = lean_profileit(v___x_2645_, v_opts_2640_, v___f_2644_, v___x_2646_);
v_snd_2648_ = lean_ctor_get(v___x_2647_, 1);
lean_inc(v_snd_2648_);
if (lean_obj_tag(v_old_x3f_2429_) == 1)
{
lean_object* v_val_2649_; lean_object* v_fst_2650_; lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v_pos_2653_; lean_object* v_toSnapshot_2654_; lean_object* v_stx_2655_; lean_object* v_parserState_2656_; lean_object* v_elabSnap_2657_; lean_object* v_nextCmdSnap_x3f_2658_; uint8_t v___x_2659_; 
v_val_2649_ = lean_ctor_get(v_old_x3f_2429_, 0);
v_fst_2650_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_n(v_fst_2650_, 2);
lean_dec(v___x_2647_);
v_fst_2651_ = lean_ctor_get(v_snd_2648_, 0);
lean_inc(v_fst_2651_);
v_snd_2652_ = lean_ctor_get(v_snd_2648_, 1);
lean_inc(v_snd_2652_);
lean_dec(v_snd_2648_);
v_pos_2653_ = lean_ctor_get(v_parserState_2430_, 0);
lean_inc(v_pos_2653_);
lean_dec_ref(v_parserState_2430_);
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
lean_inc_ref(v_opts_2640_);
lean_inc(v_fst_2650_);
lean_inc(v_fst_2651_);
v___y_2597_ = v_fst_2651_;
v___y_2598_ = v___x_2646_;
v___y_2599_ = v_fst_2650_;
v___y_2600_ = v_snd_2652_;
v___y_2601_ = v_opts_2640_;
v___y_2602_ = v_pos_2653_;
v___y_2603_ = v_fst_2651_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v_fst_2650_;
v___y_2606_ = v_opts_2640_;
goto v___jp_2596_;
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_val_2660_ = lean_ctor_get(v_nextCmdSnap_x3f_2658_, 0);
v___x_2661_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__6));
lean_inc(v_val_2660_);
v___x_2662_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_2661_, v_val_2660_);
lean_inc_ref(v_opts_2640_);
lean_inc(v_fst_2650_);
lean_inc(v_fst_2651_);
v___y_2597_ = v_fst_2651_;
v___y_2598_ = v___x_2646_;
v___y_2599_ = v_fst_2650_;
v___y_2600_ = v_snd_2652_;
v___y_2601_ = v_opts_2640_;
v___y_2602_ = v_pos_2653_;
v___y_2603_ = v_fst_2651_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v_fst_2650_;
v___y_2606_ = v_opts_2640_;
goto v___jp_2596_;
}
}
else
{
lean_inc(v_val_2649_);
lean_dec(v_pos_2653_);
lean_dec(v_snd_2652_);
lean_dec(v_fst_2650_);
lean_dec_ref_known(v_old_x3f_2429_, 1);
lean_dec_ref(v_opts_2640_);
lean_dec_ref(v_parseCancelTk_2434_);
lean_dec_ref(v_cmdState_2431_);
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
v_toSnapshot_2439_ = v_toSnapshot_2654_;
v_stx_2440_ = v_stx_2655_;
v_parserState_2441_ = v_parserState_2656_;
v_elabSnap_2442_ = v_elabSnap_2657_;
v_val_2443_ = v_val_2663_;
v_newParserState_2444_ = v_fst_2651_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2664_; 
lean_dec(v_fst_2651_);
lean_dec_ref(v_cmds_2435_);
v___x_2664_ = lean_io_promise_resolve(v_val_2649_, v_prom_2432_);
lean_dec(v_prom_2432_);
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
v_pos_2668_ = lean_ctor_get(v_parserState_2430_, 0);
lean_inc(v_pos_2668_);
lean_dec_ref(v_parserState_2430_);
lean_inc_ref(v_opts_2640_);
v___y_2597_ = v_fst_2666_;
v___y_2598_ = v___x_2646_;
v___y_2599_ = v_fst_2665_;
v___y_2600_ = v_snd_2667_;
v___y_2601_ = v_opts_2640_;
v___y_2602_ = v_pos_2668_;
v___y_2603_ = v_fst_2666_;
v___y_2604_ = v___x_2646_;
v___y_2605_ = v_fst_2665_;
v___y_2606_ = v_opts_2640_;
goto v___jp_2596_;
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
uint8_t v_val_45336__boxed_2727_; uint8_t v___x_45339__boxed_2728_; lean_object* v_res_2729_; 
v_val_45336__boxed_2727_ = lean_unbox(v_val_2704_);
v___x_45339__boxed_2728_ = lean_unbox(v___x_2708_);
v_res_2729_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___lam__5(v___x_2699_, v_val_2700_, v_cmds_2701_, v_fst_2702_, v_fst_2703_, v_val_45336__boxed_2727_, v_a_2705_, v_snd_2706_, v___x_2707_, v___x_45339__boxed_2728_, v_fst_2709_, v_val_2710_, v_val_2711_, v_val_2712_, v_snd_2713_, v_prom_2714_, v___x_2715_, v___f_2716_, v___f_2717_, v___f_2718_, v_pos_2719_, v_cmdState_2720_, v_opts_2721_, v___x_2722_, v_old_x3f_2723_, v_parseCancelTk_2724_, v_next_x3f_2725_);
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
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_3052_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_3052_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_3052_;
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
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_3051_; 
v_a_2848_ = lean_ctor_get(v_a_2840_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_2850_ = v_a_2840_;
v_isShared_2851_ = v_isSharedCheck_3051_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v_a_2840_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_3051_;
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
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_stx_2827_);
v___x_2865_ = v_reuseFailAlloc_3050_;
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
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_3041_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_3041_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_3041_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_3040_; 
v_fst_2872_ = lean_ctor_get(v_a_2868_, 0);
v_snd_2873_ = lean_ctor_get(v_a_2868_, 1);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2875_ = v_a_2868_;
v_isShared_2876_ = v_isSharedCheck_3040_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_snd_2873_);
lean_inc(v_fst_2872_);
lean_dec(v_a_2868_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_3040_;
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
double v___x_2988_; double v___x_2989_; double v___x_2990_; double v___x_2991_; double v___x_2992_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_del_object(v___x_2842_);
lean_dec_ref(v___x_2835_);
v___x_2988_ = lean_float_of_nat(v___x_2852_);
v___x_2989_ = lean_float_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__6);
v___x_2990_ = lean_float_div(v___x_2988_, v___x_2989_);
v___x_2991_ = lean_float_of_nat(v___x_2877_);
v___x_2992_ = lean_float_div(v___x_2991_, v___x_2989_);
v___x_3009_ = l_Lean_trace_profiler_output;
v___x_3010_ = l_Lean_Option_get_x3f___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__1(v_opts_2857_, v___x_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = l_Lean_trace_profiler_serve;
v___x_3012_ = l_Lean_Option_get___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__1(v_opts_2857_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Lean_instInhabitedTraceState_default;
v_traceState_2895_ = v___x_3013_;
goto v___jp_2894_;
}
else
{
goto v___jp_2993_;
}
}
else
{
lean_dec_ref_known(v___x_3010_, 1);
goto v___jp_2993_;
}
v___jp_2993_:
{
uint64_t v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_2994_ = 0ULL;
v___x_2995_ = lean_box(0);
v___x_2996_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__8));
v___x_2997_ = lean_box(0);
v___x_2998_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_withLogging___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab_spec__2_spec__2_spec__4_spec__10___closed__0));
v___x_2999_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2999_, 0, v___x_2996_);
lean_ctor_set(v___x_2999_, 1, v___x_2997_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
lean_ctor_set_float(v___x_2999_, sizeof(void*)*3, v___x_2990_);
lean_ctor_set_float(v___x_2999_, sizeof(void*)*3 + 8, v___x_2992_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*3 + 16, v___x_2863_);
v___x_3000_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__11);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_2830_);
v___x_3002_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3002_, 0, v___x_2999_);
lean_ctor_set(v___x_3002_, 1, v___x_3000_);
lean_ctor_set(v___x_3002_, 2, v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_2995_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_mk_empty_array_with_capacity(v___x_3004_);
v___x_3006_ = lean_array_push(v___x_3005_, v___x_3003_);
v___x_3007_ = l_Lean_Array_toPArray_x27___redArg(v___x_3006_);
lean_dec_ref(v___x_3006_);
v___x_3008_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set_uint64(v___x_3008_, sizeof(void*)*1, v___x_2994_);
v_traceState_2895_ = v___x_3008_;
goto v___jp_2894_;
}
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint64_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; size_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
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
v___x_3014_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_3015_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_3016_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2830_, 2);
v___x_3017_ = l_Lean_Name_num___override(v___x_3016_, v___x_2830_);
v___x_3018_ = l_Lean_Name_str___override(v___x_3017_, v___x_3014_);
v___x_3019_ = l_Lean_Name_str___override(v___x_3018_, v___x_3015_);
v___x_3020_ = l_Lean_Name_str___override(v___x_3019_, v___x_3014_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_3022_ = l_Lean_Name_str___override(v___x_3020_, v___x_3021_);
v___x_3023_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_3024_ = l_Lean_Name_str___override(v___x_3022_, v___x_3023_);
v___x_3025_ = l_Lean_Name_toString(v___x_3024_, v___x_2863_);
v___x_3026_ = lean_box(0);
v___x_3027_ = 0ULL;
v___x_3028_ = lean_unsigned_to_nat(32u);
v___x_3029_ = lean_mk_empty_array_with_capacity(v___x_3028_);
v___x_3030_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_3031_ = ((size_t)5ULL);
v___x_3032_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3032_, 0, v___x_3030_);
lean_ctor_set(v___x_3032_, 1, v___x_3029_);
lean_ctor_set(v___x_3032_, 2, v___x_2830_);
lean_ctor_set(v___x_3032_, 3, v___x_2830_);
lean_ctor_set_usize(v___x_3032_, 4, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set_uint64(v___x_3033_, sizeof(void*)*1, v___x_3027_);
v___x_3034_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3034_, 0, v___x_3025_);
lean_ctor_set(v___x_3034_, 1, v___x_2878_);
lean_ctor_set(v___x_3034_, 2, v___x_3026_);
lean_ctor_set(v___x_3034_, 3, v___x_3033_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*4, v___x_2879_);
v___x_3035_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_2835_);
v___x_3036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
lean_ctor_set(v___x_3036_, 2, v___x_3026_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_3036_);
v___x_3038_ = v___x_2842_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
v___jp_2880_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v___y_2886_);
v___x_2888_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2888_, 0, v___y_2884_);
lean_ctor_set(v___x_2888_, 1, v___x_2878_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
lean_ctor_set(v___x_2888_, 3, v___y_2885_);
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*4, v___x_2879_);
v___x_2889_ = l_Lean_Language_SnapshotTask_finished___redArg(v___y_2881_, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2890_, 0, v___y_2882_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_ctor_set(v___x_2890_, 2, v___y_2883_);
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
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_env_2903_; lean_object* v_messages_2904_; lean_object* v_scopes_2905_; lean_object* v_usedQuotCtxts_2906_; lean_object* v_nextMacroScope_2907_; lean_object* v_maxRecDepth_2908_; lean_object* v_ngen_2909_; lean_object* v_auxDeclNGen_2910_; lean_object* v_snapshotTasks_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2977_; 
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
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; lean_object* v_unused_2979_; 
v_unused_2978_ = lean_ctor_get(v___x_2902_, 9);
lean_dec(v_unused_2978_);
v_unused_2979_ = lean_ctor_get(v___x_2902_, 8);
lean_dec(v_unused_2979_);
v___x_2913_ = v___x_2902_;
v_isShared_2914_ = v_isSharedCheck_2977_;
goto v_resetjp_2912_;
}
else
{
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
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2977_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2925_; 
v___x_2915_ = lean_box(0);
v___x_2916_ = l_Lean_Options_empty;
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_unsigned_to_nat(1u);
v___x_2920_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__2));
v___x_2921_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2921_, 0, v_fst_2872_);
lean_ctor_set(v___x_2921_, 1, v___x_2915_);
lean_ctor_set(v___x_2921_, 2, v_fileMap_2831_);
lean_ctor_set(v___x_2921_, 3, v___x_2899_);
lean_ctor_set(v___x_2921_, 4, v___x_2916_);
lean_ctor_set(v___x_2921_, 5, v___x_2917_);
lean_ctor_set(v___x_2921_, 6, v___x_2918_);
lean_ctor_set(v___x_2921_, 7, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
v___x_2923_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__4));
lean_inc(v_stx_2827_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v_stx_2827_);
lean_ctor_set(v___x_2875_, 0, v___x_2923_);
v___x_2925_ = v___x_2875_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2923_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_stx_2827_);
v___x_2925_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2925_);
v___x_2927_ = lean_unsigned_to_nat(2u);
v___x_2928_ = l_Lean_Syntax_getArg(v_stx_2827_, v___x_2927_);
lean_dec(v_stx_2827_);
v___x_2929_ = l_Lean_Syntax_getArgs(v___x_2928_);
lean_dec(v___x_2928_);
v___x_2930_ = lean_array_to_list(v___x_2929_);
v___x_2931_ = l_List_mapTR_loop___at___00__private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader_spec__0(v___x_2930_, v___x_2918_);
v___x_2932_ = l_Lean_List_toPArray_x27___redArg(v___x_2931_);
v___x_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2926_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2922_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2919_);
v___x_2936_ = lean_array_push(v___x_2935_, v___x_2934_);
v___x_2937_ = l_Lean_Array_toPArray_x27___redArg(v___x_2936_);
lean_dec_ref(v___x_2936_);
lean_inc_ref(v___x_2937_);
v___x_2938_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2938_, 0, v___x_2898_);
lean_ctor_set(v___x_2938_, 1, v___x_2898_);
lean_ctor_set(v___x_2938_, 2, v___x_2937_);
lean_ctor_set_uint8(v___x_2938_, sizeof(void*)*3, v___x_2863_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 9, v_traceState_2895_);
lean_ctor_set(v___x_2913_, 8, v___x_2938_);
v___x_2940_ = v___x_2913_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_env_2903_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v_messages_2904_);
lean_ctor_set(v_reuseFailAlloc_2975_, 2, v_scopes_2905_);
lean_ctor_set(v_reuseFailAlloc_2975_, 3, v_usedQuotCtxts_2906_);
lean_ctor_set(v_reuseFailAlloc_2975_, 4, v_nextMacroScope_2907_);
lean_ctor_set(v_reuseFailAlloc_2975_, 5, v_maxRecDepth_2908_);
lean_ctor_set(v_reuseFailAlloc_2975_, 6, v_ngen_2909_);
lean_ctor_set(v_reuseFailAlloc_2975_, 7, v_auxDeclNGen_2910_);
lean_ctor_set(v_reuseFailAlloc_2975_, 8, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2975_, 9, v_traceState_2895_);
lean_ctor_set(v_reuseFailAlloc_2975_, 10, v_snapshotTasks_2911_);
v___x_2940_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; lean_object* v_size_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint64_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2830_);
lean_inc_ref(v___x_2901_);
lean_inc(v___x_2900_);
lean_inc_ref(v___x_2940_);
v___x_2942_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_2915_, v_parserState_2832_, v___x_2940_, v___x_2900_, v___x_2863_, v___x_2901_, v___x_2941_, v_a_2833_);
v___x_2943_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__2));
v___x_2944_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__4));
v___x_2945_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__6));
lean_inc_n(v___x_2830_, 3);
v___x_2946_ = l_Lean_Name_num___override(v___x_2945_, v___x_2830_);
v___x_2947_ = lean_unsigned_to_nat(32u);
v___x_2948_ = lean_mk_empty_array_with_capacity(v___x_2947_);
v___x_2949_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__14);
v___x_2950_ = ((size_t)5ULL);
v___x_2951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2948_);
lean_ctor_set(v___x_2951_, 2, v___x_2830_);
lean_ctor_set(v___x_2951_, 3, v___x_2830_);
lean_ctor_set_usize(v___x_2951_, 4, v___x_2950_);
v_size_2952_ = lean_ctor_get(v___x_2937_, 2);
lean_inc(v_size_2952_);
v___x_2953_ = l_Lean_Name_str___override(v___x_2946_, v___x_2943_);
v___x_2954_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_2834_);
v___x_2955_ = l_Lean_Name_str___override(v___x_2953_, v___x_2944_);
v___x_2956_ = l_Lean_Name_str___override(v___x_2955_, v___x_2943_);
v___x_2957_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_doElab___closed__0));
v___x_2958_ = l_Lean_Name_str___override(v___x_2956_, v___x_2957_);
v___x_2959_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___closed__5));
v___x_2960_ = l_Lean_Name_str___override(v___x_2958_, v___x_2959_);
v___x_2961_ = l_Lean_Name_toString(v___x_2960_, v___x_2863_);
v___x_2962_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_2963_ = 0ULL;
v___x_2964_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2964_, 0, v___x_2951_);
lean_ctor_set_uint64(v___x_2964_, sizeof(void*)*1, v___x_2963_);
v___x_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2901_);
v___x_2966_ = l_IO_Promise_result_x21___redArg(v___x_2900_);
lean_dec(v___x_2900_);
v___x_2967_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2834_);
lean_ctor_set(v___x_2967_, 1, v___x_2954_);
lean_ctor_set(v___x_2967_, 2, v___x_2965_);
lean_ctor_set(v___x_2967_, 3, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2940_);
lean_ctor_set(v___x_2968_, 1, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_inc_ref(v___x_2964_);
lean_inc_ref(v___x_2961_);
v___x_2970_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2970_, 0, v___x_2961_);
lean_ctor_set(v___x_2970_, 1, v___x_2962_);
lean_ctor_set(v___x_2970_, 2, v___x_2915_);
lean_ctor_set(v___x_2970_, 3, v___x_2964_);
lean_ctor_set_uint8(v___x_2970_, sizeof(void*)*4, v___x_2879_);
v___x_2971_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_2972_ = lean_nat_dec_lt(v___x_2830_, v_size_2952_);
lean_dec(v_size_2952_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
lean_dec_ref(v___x_2937_);
lean_dec(v___x_2830_);
v___x_2973_ = l_outOfBounds___redArg(v___x_2971_);
v___y_2881_ = v___x_2865_;
v___y_2882_ = v___x_2970_;
v___y_2883_ = v___x_2969_;
v___y_2884_ = v___x_2961_;
v___y_2885_ = v___x_2964_;
v___y_2886_ = v___x_2973_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2971_, v___x_2937_, v___x_2830_);
lean_dec(v___x_2830_);
lean_dec_ref(v___x_2937_);
v___y_2881_ = v___x_2865_;
v___y_2882_ = v___x_2970_;
v___y_2883_ = v___x_2969_;
v___y_2884_ = v___x_2961_;
v___y_2885_ = v___x_2964_;
v___y_2886_ = v___x_2974_;
goto v___jp_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
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
v_a_2980_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2896_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2896_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
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
v_a_3042_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_2867_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_2867_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
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
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v___x_2835_);
lean_dec(v___x_2834_);
lean_dec_ref(v_parserState_2832_);
lean_dec_ref(v_fileMap_2831_);
lean_dec(v___x_2830_);
lean_dec_ref(v_toProcessingContext_2829_);
lean_dec(v_origStx_2828_);
lean_dec(v_stx_2827_);
v_a_3053_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2839_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2839_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed(lean_object* v_setupImports_3061_, lean_object* v_stx_3062_, lean_object* v_origStx_3063_, lean_object* v_toProcessingContext_3064_, lean_object* v___x_3065_, lean_object* v_fileMap_3066_, lean_object* v_parserState_3067_, lean_object* v_a_3068_, lean_object* v___x_3069_, lean_object* v___x_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1(v_setupImports_3061_, v_stx_3062_, v_origStx_3063_, v_toProcessingContext_3064_, v___x_3065_, v_fileMap_3066_, v_parserState_3067_, v_a_3068_, v___x_3069_, v___x_3070_, v___y_3071_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v_a_3068_);
return v_res_3073_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___f_3075_; 
v___x_3074_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3075_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__0), 2, 1);
lean_closure_set(v___f_3075_, 0, v___x_3074_);
return v___f_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(lean_object* v_setupImports_3076_, lean_object* v_stx_3077_, lean_object* v_origStx_3078_, lean_object* v_parserState_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_toProcessingContext_3082_; lean_object* v_fileMap_3083_; lean_object* v_endPos_3084_; lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___f_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_toProcessingContext_3082_ = lean_ctor_get(v_a_3080_, 0);
v_fileMap_3083_ = lean_ctor_get(v_toProcessingContext_3082_, 2);
v_endPos_3084_ = lean_ctor_get(v_toProcessingContext_3082_, 3);
v___x_3085_ = l_Lean_Language_instInhabitedSnapshotLeaf;
v___f_3086_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___closed__0);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_unsigned_to_nat(0u);
lean_inc_ref_n(v_a_3080_, 2);
lean_inc_ref(v_fileMap_3083_);
lean_inc_ref(v_toProcessingContext_3082_);
v___f_3089_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___lam__1___boxed), 12, 10);
lean_closure_set(v___f_3089_, 0, v_setupImports_3076_);
lean_closure_set(v___f_3089_, 1, v_stx_3077_);
lean_closure_set(v___f_3089_, 2, v_origStx_3078_);
lean_closure_set(v___f_3089_, 3, v_toProcessingContext_3082_);
lean_closure_set(v___f_3089_, 4, v___x_3088_);
lean_closure_set(v___f_3089_, 5, v_fileMap_3083_);
lean_closure_set(v___f_3089_, 6, v_parserState_3079_);
lean_closure_set(v___f_3089_, 7, v_a_3080_);
lean_closure_set(v___f_3089_, 8, v___x_3087_);
lean_closure_set(v___f_3089_, 9, v___x_3085_);
lean_inc(v_endPos_3084_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v_endPos_3084_);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
v___x_3092_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___boxed), 5, 4);
lean_closure_set(v___x_3092_, 0, lean_box(0));
lean_closure_set(v___x_3092_, 1, v___f_3086_);
lean_closure_set(v___x_3092_, 2, v___f_3089_);
lean_closure_set(v___x_3092_, 3, v_a_3080_);
v___x_3093_ = l_Lean_Language_SnapshotTask_ofIO___redArg(v___x_3087_, v___x_3087_, v___x_3091_, v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader___boxed(lean_object* v_setupImports_3094_, lean_object* v_stx_3095_, lean_object* v_origStx_3096_, lean_object* v_parserState_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v_res_3100_; 
v_res_3100_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3094_, v_stx_3095_, v_origStx_3096_, v_parserState_3097_, v_a_3098_);
lean_dec_ref(v_a_3098_);
return v_res_3100_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = lean_box(0);
v___x_3104_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_3103_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4(void){
_start:
{
uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = 1;
v___x_3110_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__3));
v___x_3111_ = l_Lean_Name_toString(v___x_3110_, v___x_3109_);
return v___x_3111_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5(void){
_start:
{
uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3112_ = 0;
v___x_3113_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3114_ = lean_box(0);
v___x_3115_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3116_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3117_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3115_);
lean_ctor_set(v___x_3117_, 2, v___x_3114_);
lean_ctor_set(v___x_3117_, 3, v___x_3113_);
lean_ctor_set_uint8(v___x_3117_, sizeof(void*)*4, v___x_3112_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(lean_object* v_newParserState_3118_, lean_object* v_cmdState_3119_, lean_object* v_a_3120_, lean_object* v_toSnapshot_3121_, lean_object* v_newStx_3122_, lean_object* v_oldCmd_3123_){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v_diagnostics_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3153_; 
v___x_3125_ = lean_io_promise_new();
v___x_3126_ = l_IO_CancelToken_new();
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_oldCmd_3123_);
v___x_3128_ = 1;
v___x_3129_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
lean_inc_ref(v___x_3126_);
lean_inc(v___x_3125_);
lean_inc_ref(v_cmdState_3119_);
v___x_3130_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd(v___x_3127_, v_newParserState_3118_, v_cmdState_3119_, v___x_3125_, v___x_3128_, v___x_3126_, v___x_3129_, v_a_3120_);
v_diagnostics_3131_ = lean_ctor_get(v_toSnapshot_3121_, 1);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_toSnapshot_3121_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; lean_object* v_unused_3155_; lean_object* v_unused_3156_; 
v_unused_3154_ = lean_ctor_get(v_toSnapshot_3121_, 3);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_toSnapshot_3121_, 2);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_toSnapshot_3121_, 0);
lean_dec(v_unused_3156_);
v___x_3133_ = v_toSnapshot_3121_;
v_isShared_3134_ = v_isSharedCheck_3153_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_diagnostics_3131_);
lean_dec(v_toSnapshot_3121_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3153_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3135_ = lean_box(0);
v___x_3136_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__1);
v___x_3137_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3138_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3126_);
v___x_3140_ = l_IO_Promise_result_x21___redArg(v___x_3125_);
lean_dec(v___x_3125_);
v___x_3141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3135_);
lean_ctor_set(v___x_3141_, 1, v___x_3136_);
lean_ctor_set(v___x_3141_, 2, v___x_3139_);
lean_ctor_set(v___x_3141_, 3, v___x_3140_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_cmdState_3119_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
v___x_3144_ = 0;
v___x_3145_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__5);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v_newStx_3122_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 3, v___x_3138_);
lean_ctor_set(v___x_3133_, 2, v___x_3135_);
lean_ctor_set(v___x_3133_, 0, v___x_3137_);
v___x_3148_ = v___x_3133_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_diagnostics_3131_);
lean_ctor_set(v_reuseFailAlloc_3152_, 2, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3152_, 3, v___x_3138_);
v___x_3148_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_ctor_set_uint8(v___x_3148_, sizeof(void*)*4, v___x_3144_);
v___x_3149_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3146_, v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3145_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
lean_ctor_set(v___x_3150_, 2, v___x_3143_);
v___x_3151_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3135_, v___x_3150_);
return v___x_3151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed(lean_object* v_newParserState_3157_, lean_object* v_cmdState_3158_, lean_object* v_a_3159_, lean_object* v_toSnapshot_3160_, lean_object* v_newStx_3161_, lean_object* v_oldCmd_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0(v_newParserState_3157_, v_cmdState_3158_, v_a_3159_, v_toSnapshot_3160_, v_newStx_3161_, v_oldCmd_3162_);
lean_dec_ref(v_a_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(lean_object* v_newParserState_3165_, lean_object* v_a_3166_, lean_object* v_newStx_3167_, lean_object* v___x_3168_, lean_object* v_oldProcessed_3169_){
_start:
{
lean_object* v_result_x3f_3171_; 
v_result_x3f_3171_ = lean_ctor_get(v_oldProcessed_3169_, 2);
if (lean_obj_tag(v_result_x3f_3171_) == 1)
{
lean_object* v_val_3172_; lean_object* v_firstCmdSnap_3173_; lean_object* v_toSnapshot_3174_; lean_object* v_cmdState_3175_; lean_object* v_stx_x3f_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; lean_object* v___x_3180_; 
v_val_3172_ = lean_ctor_get(v_result_x3f_3171_, 0);
lean_inc(v_val_3172_);
v_firstCmdSnap_3173_ = lean_ctor_get(v_val_3172_, 1);
lean_inc_ref(v_firstCmdSnap_3173_);
v_toSnapshot_3174_ = lean_ctor_get(v_oldProcessed_3169_, 0);
lean_inc_ref(v_toSnapshot_3174_);
lean_dec_ref(v_oldProcessed_3169_);
v_cmdState_3175_ = lean_ctor_get(v_val_3172_, 0);
lean_inc_ref(v_cmdState_3175_);
lean_dec(v_val_3172_);
v_stx_x3f_3176_ = lean_ctor_get(v_firstCmdSnap_3173_, 0);
lean_inc(v_stx_x3f_3176_);
lean_inc_ref(v_a_3166_);
v___f_3177_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3177_, 0, v_newParserState_3165_);
lean_closure_set(v___f_3177_, 1, v_cmdState_3175_);
lean_closure_set(v___f_3177_, 2, v_a_3166_);
lean_closure_set(v___f_3177_, 3, v_toSnapshot_3174_);
lean_closure_set(v___f_3177_, 4, v_newStx_3167_);
v___x_3178_ = lean_box(0);
v___x_3179_ = 1;
v___x_3180_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_firstCmdSnap_3173_, v___f_3177_, v_stx_x3f_3176_, v___x_3168_, v___x_3178_, v___x_3179_);
return v___x_3180_;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v___x_3168_);
lean_dec_ref(v_newParserState_3165_);
v___x_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_newStx_3167_);
v___x_3182_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3181_, v_oldProcessed_3169_);
return v___x_3182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed(lean_object* v_newParserState_3183_, lean_object* v_a_3184_, lean_object* v_newStx_3185_, lean_object* v___x_3186_, lean_object* v_oldProcessed_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1(v_newParserState_3183_, v_a_3184_, v_newStx_3185_, v___x_3186_, v_oldProcessed_3187_);
lean_dec_ref(v_a_3184_);
return v_res_3189_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0(void){
_start:
{
uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3190_ = 0;
v___x_3191_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3192_ = lean_box(0);
v___x_3193_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3194_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3195_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___x_3193_);
lean_ctor_set(v___x_3195_, 2, v___x_3192_);
lean_ctor_set(v___x_3195_, 3, v___x_3191_);
lean_ctor_set_uint8(v___x_3195_, sizeof(void*)*4, v___x_3190_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(lean_object* v_toProcessingContext_3196_, lean_object* v_a_3197_, lean_object* v_old_3198_, lean_object* v_newStx_3199_, lean_object* v_newParserState_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_result_x3f_3203_; 
v_result_x3f_3203_ = lean_ctor_get(v_old_3198_, 4);
lean_inc(v_result_x3f_3203_);
if (lean_obj_tag(v_result_x3f_3203_) == 1)
{
lean_object* v_val_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3258_; 
v_val_3204_ = lean_ctor_get(v_result_x3f_3203_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_result_x3f_3203_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3206_ = v_result_x3f_3203_;
v_isShared_3207_ = v_isSharedCheck_3258_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_val_3204_);
lean_dec(v_result_x3f_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3258_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v_processedSnap_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3256_; 
v_processedSnap_3208_ = lean_ctor_get(v_val_3204_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_val_3204_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; 
v_unused_3257_ = lean_ctor_get(v_val_3204_, 0);
lean_dec(v_unused_3257_);
v___x_3210_ = v_val_3204_;
v_isShared_3211_ = v_isSharedCheck_3256_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_processedSnap_3208_);
lean_dec(v_val_3204_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3256_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_toSnapshot_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3251_; 
v_toSnapshot_3212_ = lean_ctor_get(v_old_3198_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_old_3198_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; 
v_unused_3252_ = lean_ctor_get(v_old_3198_, 4);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_old_3198_, 3);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_old_3198_, 2);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v_old_3198_, 1);
lean_dec(v_unused_3255_);
v___x_3214_ = v_old_3198_;
v_isShared_3215_ = v_isSharedCheck_3251_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_toSnapshot_3212_);
lean_dec(v_old_3198_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3251_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_pos_3216_; lean_object* v_endPos_3217_; lean_object* v_stx_x3f_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; lean_object* v___x_3224_; lean_object* v_diagnostics_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3247_; 
v_pos_3216_ = lean_ctor_get(v_newParserState_3200_, 0);
v_endPos_3217_ = lean_ctor_get(v_toProcessingContext_3196_, 3);
v_stx_x3f_3218_ = lean_ctor_get(v_processedSnap_3208_, 0);
lean_inc(v_stx_x3f_3218_);
lean_inc(v_endPos_3217_);
lean_inc(v_pos_3216_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_pos_3216_);
lean_ctor_set(v___x_3219_, 1, v_endPos_3217_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
lean_inc_ref(v___x_3220_);
lean_inc(v_newStx_3199_);
lean_inc_ref(v_a_3197_);
lean_inc_ref(v_newParserState_3200_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__1___boxed), 6, 4);
lean_closure_set(v___f_3221_, 0, v_newParserState_3200_);
lean_closure_set(v___f_3221_, 1, v_a_3197_);
lean_closure_set(v___f_3221_, 2, v_newStx_3199_);
lean_closure_set(v___f_3221_, 3, v___x_3220_);
v___x_3222_ = lean_box(0);
v___x_3223_ = 1;
v___x_3224_ = l_Lean_Language_SnapshotTask_bindIO___redArg(v_processedSnap_3208_, v___f_3221_, v_stx_x3f_3218_, v___x_3220_, v___x_3222_, v___x_3223_);
v_diagnostics_3225_ = lean_ctor_get(v_toSnapshot_3212_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_toSnapshot_3212_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; lean_object* v_unused_3249_; lean_object* v_unused_3250_; 
v_unused_3248_ = lean_ctor_get(v_toSnapshot_3212_, 3);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_toSnapshot_3212_, 2);
lean_dec(v_unused_3249_);
v_unused_3250_ = lean_ctor_get(v_toSnapshot_3212_, 0);
lean_dec(v_unused_3250_);
v___x_3227_ = v_toSnapshot_3212_;
v_isShared_3228_ = v_isSharedCheck_3247_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_diagnostics_3225_);
lean_dec(v_toSnapshot_3212_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3247_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3229_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3230_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 1, v___x_3224_);
lean_ctor_set(v___x_3210_, 0, v_newParserState_3200_);
v___x_3232_ = v___x_3210_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_newParserState_3200_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3224_);
v___x_3232_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3232_);
v___x_3234_ = v___x_3206_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3235_ = 0;
v___x_3236_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___closed__0);
lean_inc(v_newStx_3199_);
v___x_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3237_, 0, v_newStx_3199_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 3, v___x_3230_);
lean_ctor_set(v___x_3227_, 2, v___x_3222_);
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3239_ = v___x_3227_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_diagnostics_3225_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v___x_3230_);
v___x_3239_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*4, v___x_3235_);
v___x_3240_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3237_, v___x_3239_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 4, v___x_3234_);
lean_ctor_set(v___x_3214_, 3, v_newStx_3199_);
lean_ctor_set(v___x_3214_, 2, v_toProcessingContext_3196_);
lean_ctor_set(v___x_3214_, 1, v___x_3240_);
lean_ctor_set(v___x_3214_, 0, v___x_3236_);
v___x_3242_ = v___x_3214_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_toProcessingContext_3196_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_newStx_3199_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v___x_3234_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
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
lean_dec(v_result_x3f_3203_);
lean_dec_ref(v_newParserState_3200_);
lean_dec(v_newStx_3199_);
lean_dec_ref(v_toProcessingContext_3196_);
return v_old_3198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed(lean_object* v_toProcessingContext_3259_, lean_object* v_a_3260_, lean_object* v_old_3261_, lean_object* v_newStx_3262_, lean_object* v_newParserState_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3259_, v_a_3260_, v_old_3261_, v_newStx_3262_, v_newParserState_3263_, v___y_3264_);
lean_dec_ref(v___y_3264_);
lean_dec_ref(v_a_3260_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(lean_object* v_toProcessingContext_3267_, lean_object* v_setupImports_3268_, lean_object* v_old_x3f_3269_, lean_object* v___f_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
lean_inc_ref(v_toProcessingContext_3267_);
v___x_3273_ = l_Lean_Parser_parseHeader(v_toProcessingContext_3267_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3343_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3276_ = v___x_3273_;
v_isShared_3277_ = v_isSharedCheck_3343_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3343_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v_snd_3278_; lean_object* v_fst_3279_; lean_object* v_fst_3280_; lean_object* v_snd_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3342_; 
v_snd_3278_ = lean_ctor_get(v_a_3274_, 1);
lean_inc(v_snd_3278_);
v_fst_3279_ = lean_ctor_get(v_a_3274_, 0);
lean_inc(v_fst_3279_);
lean_dec(v_a_3274_);
v_fst_3280_ = lean_ctor_get(v_snd_3278_, 0);
v_snd_3281_ = lean_ctor_get(v_snd_3278_, 1);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_snd_3278_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3283_ = v_snd_3278_;
v_isShared_3284_ = v_isSharedCheck_3342_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_snd_3281_);
lean_inc(v_fst_3280_);
lean_dec(v_snd_3278_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3342_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
uint8_t v___x_3285_; 
v___x_3285_ = l_Lean_MessageLog_hasErrors(v_snd_3281_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; lean_object* v___y_3288_; 
lean_inc(v_fst_3279_);
v___x_3286_ = l_Lean_Syntax_unsetTrailing(v_fst_3279_);
if (lean_obj_tag(v_old_x3f_3269_) == 1)
{
lean_object* v_val_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3325_; 
v_val_3309_ = lean_ctor_get(v_old_x3f_3269_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v_old_x3f_3269_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3311_ = v_old_x3f_3269_;
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_val_3309_);
lean_dec(v_old_x3f_3269_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3325_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v_stx_3313_; lean_object* v_result_x3f_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; 
v_stx_3313_ = lean_ctor_get(v_val_3309_, 3);
v_result_x3f_3314_ = lean_ctor_get(v_val_3309_, 4);
lean_inc(v_stx_3313_);
v___x_3315_ = l_Lean_Syntax_unsetTrailing(v_stx_3313_);
lean_inc(v___x_3286_);
v___x_3316_ = l_Lean_Syntax_eqWithInfo(v___x_3286_, v___x_3315_);
if (v___x_3316_ == 0)
{
lean_inc(v_result_x3f_3314_);
lean_del_object(v___x_3311_);
lean_dec(v_val_3309_);
lean_dec_ref(v___f_3270_);
if (lean_obj_tag(v_result_x3f_3314_) == 0)
{
v___y_3288_ = v___y_3271_;
goto v___jp_3287_;
}
else
{
lean_object* v_val_3317_; lean_object* v_processedSnap_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_val_3317_ = lean_ctor_get(v_result_x3f_3314_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v_result_x3f_3314_, 1);
v_processedSnap_3318_ = lean_ctor_get(v_val_3317_, 1);
lean_inc_ref(v_processedSnap_3318_);
lean_dec(v_val_3317_);
v___x_3319_ = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot;
v___x_3320_ = l_Lean_Language_SnapshotTask_cancelRec___redArg(v___x_3319_, v_processedSnap_3318_);
v___y_3288_ = v___y_3271_;
goto v___jp_3287_;
}
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3323_; 
lean_dec(v___x_3286_);
lean_del_object(v___x_3283_);
lean_dec(v_snd_3281_);
lean_del_object(v___x_3276_);
lean_dec_ref(v_setupImports_3268_);
lean_dec_ref(v_toProcessingContext_3267_);
lean_inc_ref(v___y_3271_);
v___x_3321_ = lean_apply_5(v___f_3270_, v_val_3309_, v_fst_3279_, v_fst_3280_, v___y_3271_, lean_box(0));
if (v_isShared_3312_ == 0)
{
lean_ctor_set_tag(v___x_3311_, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3321_);
v___x_3323_ = v___x_3311_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_dec_ref(v___f_3270_);
lean_dec(v_old_x3f_3269_);
v___y_3288_ = v___y_3271_;
goto v___jp_3287_;
}
v___jp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3289_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3281_);
lean_inc(v_fst_3280_);
lean_inc(v_fst_3279_);
v___x_3290_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_processHeader(v_setupImports_3268_, v___x_3286_, v_fst_3279_, v_fst_3280_, v___y_3288_);
v___x_3291_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3292_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_unsigned_to_nat(32u);
v___x_3295_ = lean_mk_empty_array_with_capacity(v___x_3294_);
lean_dec_ref(v___x_3295_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3290_);
v___x_3298_ = v___x_3283_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_fst_3280_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3290_);
v___x_3298_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3300_, 0, v___x_3291_);
lean_ctor_set(v___x_3300_, 1, v___x_3292_);
lean_ctor_set(v___x_3300_, 2, v___x_3293_);
lean_ctor_set(v___x_3300_, 3, v___x_3296_);
lean_ctor_set_uint8(v___x_3300_, sizeof(void*)*4, v___x_3285_);
lean_inc(v_fst_3279_);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_fst_3279_);
v___x_3302_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3302_, 0, v___x_3291_);
lean_ctor_set(v___x_3302_, 1, v___x_3289_);
lean_ctor_set(v___x_3302_, 2, v___x_3293_);
lean_ctor_set(v___x_3302_, 3, v___x_3296_);
lean_ctor_set_uint8(v___x_3302_, sizeof(void*)*4, v___x_3285_);
v___x_3303_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3301_, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3300_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
lean_ctor_set(v___x_3304_, 2, v_toProcessingContext_3267_);
lean_ctor_set(v___x_3304_, 3, v_fst_3279_);
lean_ctor_set(v___x_3304_, 4, v___x_3299_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3304_);
v___x_3306_ = v___x_3276_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
lean_del_object(v___x_3283_);
lean_dec(v_fst_3280_);
lean_dec_ref(v___f_3270_);
lean_dec(v_old_x3f_3269_);
lean_dec_ref(v_setupImports_3268_);
v___x_3326_ = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(v_snd_3281_);
v___x_3327_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__4);
v___x_3328_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_unsigned_to_nat(32u);
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_3330_);
lean_dec_ref(v___x_3331_);
v___x_3332_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3333_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3333_, 0, v___x_3327_);
lean_ctor_set(v___x_3333_, 1, v___x_3328_);
lean_ctor_set(v___x_3333_, 2, v___x_3329_);
lean_ctor_set(v___x_3333_, 3, v___x_3332_);
lean_ctor_set_uint8(v___x_3333_, sizeof(void*)*4, v___x_3285_);
lean_inc(v_fst_3279_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_fst_3279_);
v___x_3335_ = 0;
v___x_3336_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3336_, 0, v___x_3327_);
lean_ctor_set(v___x_3336_, 1, v___x_3326_);
lean_ctor_set(v___x_3336_, 2, v___x_3329_);
lean_ctor_set(v___x_3336_, 3, v___x_3332_);
lean_ctor_set_uint8(v___x_3336_, sizeof(void*)*4, v___x_3335_);
v___x_3337_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3334_, v___x_3336_);
v___x_3338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3333_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
lean_ctor_set(v___x_3338_, 2, v_toProcessingContext_3267_);
lean_ctor_set(v___x_3338_, 3, v_fst_3279_);
lean_ctor_set(v___x_3338_, 4, v___x_3329_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 0, v___x_3338_);
v___x_3340_ = v___x_3276_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref(v___f_3270_);
lean_dec(v_old_x3f_3269_);
lean_dec_ref(v_setupImports_3268_);
lean_dec_ref(v_toProcessingContext_3267_);
v_a_3344_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3273_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3273_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
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
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed(lean_object* v_toProcessingContext_3352_, lean_object* v_setupImports_3353_, lean_object* v_old_x3f_3354_, lean_object* v___f_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3(v_toProcessingContext_3352_, v_setupImports_3353_, v_old_x3f_3354_, v___f_3355_, v___y_3356_);
lean_dec_ref(v___y_3356_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4(lean_object* v___x_3359_, lean_object* v_toProcessingContext_3360_, lean_object* v_x_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3362_ = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(v___x_3359_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3365_, 0, v_x_3361_);
lean_ctor_set(v___x_3365_, 1, v___x_3362_);
lean_ctor_set(v___x_3365_, 2, v_toProcessingContext_3360_);
lean_ctor_set(v___x_3365_, 3, v___x_3363_);
lean_ctor_set(v___x_3365_, 4, v___x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(lean_object* v_setupImports_3366_, lean_object* v_old_x3f_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_toProcessingContext_3370_; lean_object* v___x_3371_; lean_object* v___f_3372_; lean_object* v___f_3373_; lean_object* v___f_3374_; 
v_toProcessingContext_3370_ = lean_ctor_get(v_a_3368_, 0);
v___x_3371_ = l_Lean_Language_instInhabitedSnapshotLeaf;
lean_inc_ref(v_a_3368_);
lean_inc_ref_n(v_toProcessingContext_3370_, 3);
v___f_3372_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3372_, 0, v_toProcessingContext_3370_);
lean_closure_set(v___f_3372_, 1, v_a_3368_);
lean_inc(v_old_x3f_3367_);
v___f_3373_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__3___boxed), 6, 4);
lean_closure_set(v___f_3373_, 0, v_toProcessingContext_3370_);
lean_closure_set(v___f_3373_, 1, v_setupImports_3366_);
lean_closure_set(v___f_3373_, 2, v_old_x3f_3367_);
lean_closure_set(v___f_3373_, 3, v___f_3372_);
v___f_3374_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__4), 3, 2);
lean_closure_set(v___f_3374_, 0, v___x_3371_);
lean_closure_set(v___f_3374_, 1, v_toProcessingContext_3370_);
if (lean_obj_tag(v_old_x3f_3367_) == 1)
{
lean_object* v_val_3375_; lean_object* v_result_x3f_3376_; 
v_val_3375_ = lean_ctor_get(v_old_x3f_3367_, 0);
lean_inc(v_val_3375_);
lean_dec_ref_known(v_old_x3f_3367_, 1);
v_result_x3f_3376_ = lean_ctor_get(v_val_3375_, 4);
if (lean_obj_tag(v_result_x3f_3376_) == 1)
{
lean_object* v_stx_3377_; lean_object* v_val_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_stx_3377_ = lean_ctor_get(v_val_3375_, 3);
lean_inc(v_stx_3377_);
v_val_3378_ = lean_ctor_get(v_result_x3f_3376_, 0);
lean_inc(v_val_3375_);
v___x_3379_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v_val_3375_);
v___x_3380_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v___x_3379_);
if (lean_obj_tag(v___x_3380_) == 1)
{
lean_object* v_val_3381_; 
v_val_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v___x_3380_, 1);
if (lean_obj_tag(v_val_3381_) == 1)
{
lean_object* v_val_3382_; lean_object* v_firstCmdSnap_3383_; lean_object* v___x_3384_; 
v_val_3382_ = lean_ctor_get(v_val_3381_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_val_3381_, 1);
v_firstCmdSnap_3383_ = lean_ctor_get(v_val_3382_, 1);
lean_inc_ref(v_firstCmdSnap_3383_);
lean_dec(v_val_3382_);
v___x_3384_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_firstCmdSnap_3383_);
if (lean_obj_tag(v___x_3384_) == 1)
{
lean_object* v_val_3385_; lean_object* v_nextCmdSnap_x3f_3386_; 
v_val_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_val_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v_nextCmdSnap_x3f_3386_ = lean_ctor_get(v_val_3385_, 4);
lean_inc(v_nextCmdSnap_x3f_3386_);
lean_dec(v_val_3385_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3386_) == 0)
{
lean_object* v___x_3387_; 
lean_dec(v_stx_3377_);
lean_dec(v_val_3375_);
v___x_3387_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3387_;
}
else
{
lean_object* v_val_3388_; lean_object* v___x_3389_; 
v_val_3388_ = lean_ctor_get(v_nextCmdSnap_x3f_3386_, 0);
lean_inc(v_val_3388_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3386_, 1);
v___x_3389_ = l_Lean_Language_SnapshotTask_get_x3f___redArg(v_val_3388_);
if (lean_obj_tag(v___x_3389_) == 1)
{
lean_object* v_val_3390_; lean_object* v_parserState_3391_; lean_object* v_pos_3392_; uint8_t v___x_3393_; 
v_val_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_val_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v_parserState_3391_ = lean_ctor_get(v_val_3390_, 2);
lean_inc_ref(v_parserState_3391_);
lean_dec(v_val_3390_);
v_pos_3392_ = lean_ctor_get(v_parserState_3391_, 0);
lean_inc(v_pos_3392_);
lean_dec_ref(v_parserState_3391_);
v___x_3393_ = l_Lean_Language_Lean_isBeforeEditPos(v_pos_3392_, v_a_3368_);
lean_dec(v_pos_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec(v_stx_3377_);
lean_dec(v_val_3375_);
v___x_3394_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3394_;
}
else
{
lean_object* v_parserState_3395_; lean_object* v___x_3396_; 
lean_dec_ref(v___f_3374_);
lean_dec_ref(v___f_3373_);
v_parserState_3395_ = lean_ctor_get(v_val_3378_, 0);
lean_inc_ref(v_parserState_3395_);
lean_inc_ref(v_toProcessingContext_3370_);
v___x_3396_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__2(v_toProcessingContext_3370_, v_a_3368_, v_val_3375_, v_stx_3377_, v_parserState_3395_, v_a_3368_);
return v___x_3396_;
}
}
else
{
lean_object* v___x_3397_; 
lean_dec(v___x_3389_);
lean_dec(v_stx_3377_);
lean_dec(v_val_3375_);
v___x_3397_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3397_;
}
}
}
else
{
lean_object* v___x_3398_; 
lean_dec(v___x_3384_);
lean_dec(v_stx_3377_);
lean_dec(v_val_3375_);
v___x_3398_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3398_;
}
}
else
{
lean_object* v___x_3399_; 
lean_dec(v_val_3381_);
lean_dec(v_stx_3377_);
lean_dec(v_val_3375_);
v___x_3399_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3399_;
}
}
else
{
lean_object* v___x_3400_; 
lean_dec(v___x_3380_);
lean_dec(v_stx_3377_);
lean_dec(v_val_3375_);
v___x_3400_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3400_;
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v_val_3375_);
v___x_3401_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3401_;
}
}
else
{
lean_object* v___x_3402_; 
lean_dec(v_old_x3f_3367_);
v___x_3402_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg(v___f_3374_, v___f_3373_, v_a_3368_);
return v___x_3402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed(lean_object* v_setupImports_3403_, lean_object* v_old_x3f_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader(v_setupImports_3403_, v_old_x3f_3404_, v_a_3405_);
lean_dec_ref(v_a_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* v_setupImports_3408_, lean_object* v_old_x3f_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v___x_3412_; 
lean_inc(v_old_x3f_3409_);
v___x_3412_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___boxed), 4, 2);
lean_closure_set(v___x_3412_, 0, v_setupImports_3408_);
lean_closure_set(v___x_3412_, 1, v_old_x3f_3409_);
if (lean_obj_tag(v_old_x3f_3409_) == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_box(0);
v___x_3414_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3412_, v___x_3413_, v_a_3410_);
return v___x_3414_;
}
else
{
lean_object* v_val_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3424_; 
v_val_3415_ = lean_ctor_get(v_old_x3f_3409_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_old_x3f_3409_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3417_ = v_old_x3f_3409_;
v_isShared_3418_ = v_isSharedCheck_3424_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_val_3415_);
lean_dec(v_old_x3f_3409_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3424_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_ictx_3419_; lean_object* v___x_3421_; 
v_ictx_3419_ = lean_ctor_get(v_val_3415_, 2);
lean_inc_ref(v_ictx_3419_);
lean_dec(v_val_3415_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v_ictx_3419_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_ictx_3419_);
v___x_3421_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___x_3412_, v___x_3421_, v_a_3410_);
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process___boxed(lean_object* v_setupImports_3425_, lean_object* v_old_x3f_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Language_Lean_process(v_setupImports_3425_, v_old_x3f_3426_, v_a_3427_);
lean_dec_ref(v_a_3427_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* v_inputCtx_3430_, lean_object* v_parserState_3431_, lean_object* v_commandState_3432_, lean_object* v_old_x3f_3433_){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3443_; 
v___x_3435_ = lean_io_promise_new();
v___x_3436_ = l_IO_CancelToken_new();
if (lean_obj_tag(v_old_x3f_3433_) == 0)
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_box(0);
v___y_3443_ = v___x_3458_;
goto v___jp_3442_;
}
else
{
lean_object* v_val_3459_; lean_object* v_snd_3460_; lean_object* v___x_3461_; 
v_val_3459_ = lean_ctor_get(v_old_x3f_3433_, 0);
v_snd_3460_ = lean_ctor_get(v_val_3459_, 1);
lean_inc(v_snd_3460_);
v___x_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3461_, 0, v_snd_3460_);
v___y_3443_ = v___x_3461_;
goto v___jp_3442_;
}
v___jp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3440_ = l_Lean_Language_Lean_LeanProcessingM_run___redArg(v___y_3438_, v___y_3439_, v_inputCtx_3430_);
lean_dec(v___x_3440_);
v___x_3441_ = l_IO_Promise_result_x21___redArg(v___x_3435_);
lean_dec(v___x_3435_);
return v___x_3441_;
}
v___jp_3442_:
{
uint8_t v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3444_ = 1;
v___x_3445_ = ((lean_object*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseHeader___lam__0___closed__0));
v___x_3446_ = lean_box(v___x_3444_);
lean_inc(v___x_3435_);
v___x_3447_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___boxed), 9, 7);
lean_closure_set(v___x_3447_, 0, v___y_3443_);
lean_closure_set(v___x_3447_, 1, v_parserState_3431_);
lean_closure_set(v___x_3447_, 2, v_commandState_3432_);
lean_closure_set(v___x_3447_, 3, v___x_3435_);
lean_closure_set(v___x_3447_, 4, v___x_3446_);
lean_closure_set(v___x_3447_, 5, v___x_3436_);
lean_closure_set(v___x_3447_, 6, v___x_3445_);
if (lean_obj_tag(v_old_x3f_3433_) == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_box(0);
v___y_3438_ = v___x_3447_;
v___y_3439_ = v___x_3448_;
goto v___jp_3437_;
}
else
{
lean_object* v_val_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3457_; 
v_val_3449_ = lean_ctor_get(v_old_x3f_3433_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_old_x3f_3433_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3451_ = v_old_x3f_3433_;
v_isShared_3452_ = v_isSharedCheck_3457_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_val_3449_);
lean_dec(v_old_x3f_3433_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3457_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_fst_3453_; lean_object* v___x_3455_; 
v_fst_3453_ = lean_ctor_get(v_val_3449_, 0);
lean_inc(v_fst_3453_);
lean_dec(v_val_3449_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v_fst_3453_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_fst_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
v___y_3438_ = v___x_3447_;
v___y_3439_ = v___x_3455_;
goto v___jp_3437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands___boxed(lean_object* v_inputCtx_3462_, lean_object* v_parserState_3463_, lean_object* v_commandState_3464_, lean_object* v_old_x3f_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_Language_Lean_processCommands(v_inputCtx_3462_, v_parserState_3463_, v_commandState_3464_, v_old_x3f_3465_);
lean_dec_ref(v_inputCtx_3462_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(lean_object* v_snap_3468_){
_start:
{
lean_object* v_nextCmdSnap_x3f_3469_; 
v_nextCmdSnap_x3f_3469_ = lean_ctor_get(v_snap_3468_, 4);
if (lean_obj_tag(v_nextCmdSnap_x3f_3469_) == 1)
{
lean_object* v_val_3470_; lean_object* v___x_3471_; 
lean_inc_ref(v_nextCmdSnap_x3f_3469_);
lean_dec_ref(v_snap_3468_);
v_val_3470_ = lean_ctor_get(v_nextCmdSnap_x3f_3469_, 0);
lean_inc(v_val_3470_);
lean_dec_ref_known(v_nextCmdSnap_x3f_3469_, 1);
v___x_3471_ = l_Lean_Language_SnapshotTask_get___redArg(v_val_3470_);
v_snap_3468_ = v___x_3471_;
goto _start;
}
else
{
lean_object* v_elabSnap_3473_; lean_object* v_resultSnap_3474_; lean_object* v___x_3475_; lean_object* v_cmdState_3476_; lean_object* v___x_3477_; 
v_elabSnap_3473_ = lean_ctor_get(v_snap_3468_, 3);
lean_inc_ref(v_elabSnap_3473_);
lean_dec_ref(v_snap_3468_);
v_resultSnap_3474_ = lean_ctor_get(v_elabSnap_3473_, 2);
lean_inc_ref(v_resultSnap_3474_);
lean_dec_ref(v_elabSnap_3473_);
v___x_3475_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_3474_);
v_cmdState_3476_ = lean_ctor_get(v___x_3475_, 1);
lean_inc_ref(v_cmdState_3476_);
lean_dec(v___x_3475_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_cmdState_3476_);
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object* v_snap_3478_){
_start:
{
lean_object* v_result_x3f_3479_; 
v_result_x3f_3479_ = lean_ctor_get(v_snap_3478_, 4);
lean_inc(v_result_x3f_3479_);
lean_dec_ref(v_snap_3478_);
if (lean_obj_tag(v_result_x3f_3479_) == 0)
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_box(0);
return v___x_3480_;
}
else
{
lean_object* v_val_3481_; lean_object* v_processedSnap_3482_; lean_object* v___x_3483_; lean_object* v_result_x3f_3484_; 
v_val_3481_ = lean_ctor_get(v_result_x3f_3479_, 0);
lean_inc(v_val_3481_);
lean_dec_ref_known(v_result_x3f_3479_, 1);
v_processedSnap_3482_ = lean_ctor_get(v_val_3481_, 1);
lean_inc_ref(v_processedSnap_3482_);
lean_dec(v_val_3481_);
v___x_3483_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3482_);
v_result_x3f_3484_ = lean_ctor_get(v___x_3483_, 2);
lean_inc(v_result_x3f_3484_);
lean_dec(v___x_3483_);
if (lean_obj_tag(v_result_x3f_3484_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_box(0);
return v___x_3485_;
}
else
{
lean_object* v_val_3486_; lean_object* v_firstCmdSnap_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_val_3486_ = lean_ctor_get(v_result_x3f_3484_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v_result_x3f_3484_, 1);
v_firstCmdSnap_3487_ = lean_ctor_get(v_val_3486_, 1);
lean_inc_ref(v_firstCmdSnap_3487_);
lean_dec(v_val_3486_);
v___x_3488_ = l_Lean_Language_SnapshotTask_get___redArg(v_firstCmdSnap_3487_);
v___x_3489_ = l___private_Lean_Language_Lean_0__Lean_Language_Lean_waitForFinalCmdState_x3f_goCmd(v___x_3488_);
return v___x_3489_;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__2(void){
_start:
{
uint8_t v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = 1;
v___x_3496_ = ((lean_object*)(l_Lean_Language_Lean_truncateToHeader___closed__1));
v___x_3497_ = l_Lean_Name_toString(v___x_3496_, v___x_3495_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__3(void){
_start:
{
uint8_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3498_ = 0;
v___x_3499_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___redArg___closed__16);
v___x_3500_ = lean_box(0);
v___x_3501_ = l_Lean_Language_Snapshot_Diagnostics_empty;
v___x_3502_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__2, &l_Lean_Language_Lean_truncateToHeader___closed__2_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__2);
v___x_3503_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3503_, 0, v___x_3502_);
lean_ctor_set(v___x_3503_, 1, v___x_3501_);
lean_ctor_set(v___x_3503_, 2, v___x_3500_);
lean_ctor_set(v___x_3503_, 3, v___x_3499_);
lean_ctor_set_uint8(v___x_3503_, sizeof(void*)*4, v___x_3498_);
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_Language_Lean_truncateToHeader___closed__4(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
v___x_3505_ = lean_box(0);
v___x_3506_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3505_, v___x_3504_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object* v_snap_3507_){
_start:
{
lean_object* v_result_x3f_3508_; 
v_result_x3f_3508_ = lean_ctor_get(v_snap_3507_, 4);
lean_inc(v_result_x3f_3508_);
if (lean_obj_tag(v_result_x3f_3508_) == 1)
{
lean_object* v_val_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3583_; 
v_val_3509_ = lean_ctor_get(v_result_x3f_3508_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_result_x3f_3508_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3511_ = v_result_x3f_3508_;
v_isShared_3512_ = v_isSharedCheck_3583_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_val_3509_);
lean_dec(v_result_x3f_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3583_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_toSnapshot_3513_; lean_object* v_metaSnap_3514_; lean_object* v_ictx_3515_; lean_object* v_stx_3516_; lean_object* v_parserState_3517_; lean_object* v_processedSnap_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3582_; 
v_toSnapshot_3513_ = lean_ctor_get(v_snap_3507_, 0);
v_metaSnap_3514_ = lean_ctor_get(v_snap_3507_, 1);
v_ictx_3515_ = lean_ctor_get(v_snap_3507_, 2);
v_stx_3516_ = lean_ctor_get(v_snap_3507_, 3);
v_parserState_3517_ = lean_ctor_get(v_val_3509_, 0);
v_processedSnap_3518_ = lean_ctor_get(v_val_3509_, 1);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_val_3509_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3520_ = v_val_3509_;
v_isShared_3521_ = v_isSharedCheck_3582_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_processedSnap_3518_);
lean_inc(v_parserState_3517_);
lean_dec(v_val_3509_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3582_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v_processed_3522_; lean_object* v_result_x3f_3523_; 
v_processed_3522_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_3518_);
v_result_x3f_3523_ = lean_ctor_get(v_processed_3522_, 2);
lean_inc(v_result_x3f_3523_);
if (lean_obj_tag(v_result_x3f_3523_) == 1)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3576_; 
lean_inc(v_stx_3516_);
lean_inc_ref(v_ictx_3515_);
lean_inc_ref(v_metaSnap_3514_);
lean_inc_ref(v_toSnapshot_3513_);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_snap_3507_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; 
v_unused_3577_ = lean_ctor_get(v_snap_3507_, 4);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_snap_3507_, 3);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_snap_3507_, 2);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_snap_3507_, 1);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_snap_3507_, 0);
lean_dec(v_unused_3581_);
v___x_3525_ = v_snap_3507_;
v_isShared_3526_ = v_isSharedCheck_3576_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v_snap_3507_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3576_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v_val_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3575_; 
v_val_3527_ = lean_ctor_get(v_result_x3f_3523_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v_result_x3f_3523_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3529_ = v_result_x3f_3523_;
v_isShared_3530_ = v_isSharedCheck_3575_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_val_3527_);
lean_dec(v_result_x3f_3523_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3575_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_toSnapshot_3531_; lean_object* v_metaSnap_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3573_; 
v_toSnapshot_3531_ = lean_ctor_get(v_processed_3522_, 0);
v_metaSnap_3532_ = lean_ctor_get(v_processed_3522_, 1);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_processed_3522_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; 
v_unused_3574_ = lean_ctor_get(v_processed_3522_, 2);
lean_dec(v_unused_3574_);
v___x_3534_ = v_processed_3522_;
v_isShared_3535_ = v_isSharedCheck_3573_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_metaSnap_3532_);
lean_inc(v_toSnapshot_3531_);
lean_dec(v_processed_3522_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3573_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v_cmdState_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3571_; 
v_cmdState_3536_ = lean_ctor_get(v_val_3527_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_val_3527_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v_val_3527_, 1);
lean_dec(v_unused_3572_);
v___x_3538_ = v_val_3527_;
v_isShared_3539_ = v_isSharedCheck_3571_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_cmdState_3536_);
lean_dec(v_val_3527_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3571_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v_resultSnap_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v_elabSnap_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v_termCmd_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3540_ = lean_box(0);
v___x_3541_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__3, &l_Lean_Language_Lean_truncateToHeader___closed__3_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__3);
lean_inc_ref(v_cmdState_3536_);
v_resultSnap_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_resultSnap_3542_, 0, v___x_3541_);
lean_ctor_set(v_resultSnap_3542_, 1, v_cmdState_3536_);
v___x_3543_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__0);
v___x_3544_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3540_, v_resultSnap_3542_);
v___x_3545_ = lean_obj_once(&l_Lean_Language_Lean_truncateToHeader___closed__4, &l_Lean_Language_Lean_truncateToHeader___closed__4_once, _init_l_Lean_Language_Lean_truncateToHeader___closed__4);
v___x_3546_ = lean_obj_once(&l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1, &l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1_once, _init_l___private_Lean_Language_Lean_0__Lean_Language_Lean_process_parseCmd___closed__1);
v_elabSnap_3547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_elabSnap_3547_, 0, v___x_3541_);
lean_ctor_set(v_elabSnap_3547_, 1, v___x_3543_);
lean_ctor_set(v_elabSnap_3547_, 2, v___x_3544_);
lean_ctor_set(v_elabSnap_3547_, 3, v___x_3545_);
lean_ctor_set(v_elabSnap_3547_, 4, v___x_3546_);
v___x_3548_ = lean_box(0);
v___x_3549_ = l_Lean_Parser_instInhabitedModuleParserState_default;
v_termCmd_3550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_termCmd_3550_, 0, v___x_3541_);
lean_ctor_set(v_termCmd_3550_, 1, v___x_3548_);
lean_ctor_set(v_termCmd_3550_, 2, v___x_3549_);
lean_ctor_set(v_termCmd_3550_, 3, v_elabSnap_3547_);
lean_ctor_set(v_termCmd_3550_, 4, v___x_3540_);
v___x_3551_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3540_, v_termCmd_3550_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 1, v___x_3551_);
v___x_3553_ = v___x_3538_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_cmdState_3536_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
lean_object* v___x_3555_; 
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3553_);
v___x_3555_ = v___x_3529_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v_newProcessed_3557_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 2, v___x_3555_);
v_newProcessed_3557_ = v___x_3534_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_toSnapshot_3531_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_metaSnap_3532_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v___x_3555_);
v_newProcessed_3557_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_3540_, v_newProcessed_3557_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 1, v___x_3558_);
v___x_3560_ = v___x_3520_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_parserState_3517_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3562_; 
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3560_);
v___x_3562_ = v___x_3511_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 4, v___x_3562_);
v___x_3564_ = v___x_3525_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_toSnapshot_3513_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_metaSnap_3514_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_ictx_3515_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_stx_3516_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
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
lean_dec(v_result_x3f_3523_);
lean_dec(v_processed_3522_);
lean_del_object(v___x_3520_);
lean_dec_ref(v_parserState_3517_);
lean_del_object(v___x_3511_);
return v_snap_3507_;
}
}
}
}
else
{
lean_dec(v_result_x3f_3508_);
return v_snap_3507_;
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

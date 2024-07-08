// Lean compiler output
// Module: Lean.Language.Lean
// Imports: Lean.Language.Basic Lean.Parser.Module Lean.Elab.Command Lean.Elab.Import
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
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Language_Lean_SetupImportsResult_trustLevel___default;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
static lean_object* l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3;
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__3___closed__1;
LEAN_EXPORT uint8_t l_Lean_Language_Lean_HeaderProcessedSnapshot_isFatal___default(lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot(lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__4;
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8;
lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2___boxed(lean_object*);
lean_object* lean_io_promise_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_data___boxed(lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalEnv_x3f(lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_ofIO___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__1;
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1;
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__6;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*);
lean_object* lean_io_promise_result(lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2;
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__7;
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__3___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_data(lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
uint8_t l_String_isEmpty(lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
lean_object* l_IO_CancelToken_new(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalEnv_x3f_goCmd(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toPArray_x27___rarg(lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__1(lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__2___closed__4;
lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__5;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__10;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_nextCmdSnap_x3f___boxed(lean_object*);
lean_object* l_panic___at_String_fromUTF8_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1(lean_object*);
static lean_object* l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__1;
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
static size_t l_Lean_Language_Lean_process_doElab___lambda__2___closed__2;
lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_Language_Lean_process_doElab___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___closed__1;
extern lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withLoggingExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot(lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__4;
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2;
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__9;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Language_Lean_HeaderParsedSnapshot_isFatal___default(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__12;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__4(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_stderrAsMessages;
lean_object* l_Lean_Language_SnapshotTask_get_x3f___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__8;
lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__3;
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__5;
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__2;
static lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6;
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt(lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__2___closed__3;
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__2;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderProcessedSnapshot_isFatal___default___boxed(lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__3___closed__4;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_isFatal___default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_Language_Lean_process_doElab___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_doElab___lambda__2___closed__1;
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5;
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__11;
lean_object* l_Lean_Language_SnapshotTask_map___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__6;
lean_object* l_Lean_Language_SnapshotTask_get___rarg(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___closed__8;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__2;
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object*);
static lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__8___closed__1;
static lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_nextCmdSnap_x3f(lean_object*);
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_Language_Lean_process_doElab___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(lean_object*);
static lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1;
lean_object* l_Lean_Language_SnapshotTask_pure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Language_instTypeNameSnapshotLeaf;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderrAsMessages", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("server", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(server) capture output to the Lean stderr channel (such as from `dbg_trace`) during elaboration of a command as a diagnostic message", 133, 133);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__3;
x_3 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Language", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__6;
x_2 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__7;
x_3 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1;
x_4 = l_Lean_Name_mkStr4(x_1, x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__2;
x_3 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__5;
x_4 = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__8;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_data(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_data___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_CommandParsedSnapshot_data(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_nextCmdSnap_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_CommandParsedSnapshot_nextCmdSnap_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_CommandParsedSnapshot_nextCmdSnap_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__1;
x_7 = 1;
x_8 = l_Lean_Language_SnapshotTask_map___rarg(x_3, x_6, x_5, x_7);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__2;
x_11 = l_Lean_Language_SnapshotTask_map___rarg(x_4, x_10, x_9, x_7);
x_12 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3;
x_13 = lean_array_push(x_12, x_8);
x_14 = lean_array_push(x_13, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__4(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__4), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_10 = 1;
x_11 = l_Lean_Language_SnapshotTask_map___rarg(x_6, x_9, x_8, x_10);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2;
x_14 = l_Lean_Language_SnapshotTask_map___rarg(x_7, x_13, x_12, x_10);
x_15 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3;
x_16 = lean_array_push(x_15, x_11);
x_17 = lean_array_push(x_16, x_14);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_18, x_17);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_24 = l_Lean_Language_SnapshotTask_map___rarg(x_21, x_23, x_22, x_10);
lean_ctor_set(x_4, 0, x_24);
x_25 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_4, x_17);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_29 = l_Lean_Language_SnapshotTask_map___rarg(x_26, x_28, x_27, x_10);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_30, x_17);
lean_ctor_set(x_1, 1, x_31);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 4);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1;
x_39 = 1;
x_40 = l_Lean_Language_SnapshotTask_map___rarg(x_35, x_38, x_37, x_39);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
x_42 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2;
x_43 = l_Lean_Language_SnapshotTask_map___rarg(x_36, x_42, x_41, x_39);
x_44 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3;
x_45 = lean_array_push(x_44, x_40);
x_46 = lean_array_push(x_45, x_43);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_box(0);
x_48 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_47, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_33, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_51 = x_33;
} else {
 lean_dec_ref(x_33);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_54 = l_Lean_Language_SnapshotTask_map___rarg(x_50, x_53, x_52, x_39);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
x_56 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_55, x_46);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_34);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_Lean_HeaderProcessedSnapshot_isFatal___default(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderProcessedSnapshot_isFatal___default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Language_Lean_HeaderProcessedSnapshot_isFatal___default(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_3 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_16 = 1;
x_17 = l_Lean_Language_SnapshotTask_map___rarg(x_13, x_15, x_14, x_16);
lean_ctor_set(x_2, 0, x_17);
x_18 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_19 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_2, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_24 = 1;
x_25 = l_Lean_Language_SnapshotTask_map___rarg(x_21, x_23, x_22, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_28 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_26, x_27);
lean_ctor_set(x_1, 1, x_28);
return x_1;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_31 = x_2;
} else {
 lean_dec_ref(x_2);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_35 = 1;
x_36 = l_Lean_Language_SnapshotTask_map___rarg(x_32, x_34, x_33, x_35);
if (lean_is_scalar(x_31)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_31;
}
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_39 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_37, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Language_Lean_HeaderParsedSnapshot_isFatal___default(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_isFatal___default___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Language_Lean_HeaderParsedSnapshot_isFatal___default(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_6, x_1);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_9, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_19 = 1;
x_20 = l_Lean_Language_SnapshotTask_map___rarg(x_16, x_18, x_17, x_19);
lean_ctor_set(x_3, 0, x_20);
x_21 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_3, x_1);
lean_ctor_set(x_2, 1, x_21);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_26 = 1;
x_27 = l_Lean_Language_SnapshotTask_map___rarg(x_23, x_25, x_24, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_28, x_1);
lean_ctor_set(x_2, 1, x_29);
return x_2;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_32 = x_3;
} else {
 lean_dec_ref(x_3);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3;
x_36 = 1;
x_37 = l_Lean_Language_SnapshotTask_map___rarg(x_33, x_35, x_34, x_36);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_38, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_11 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = 1;
x_14 = l_Lean_Language_SnapshotTask_map___rarg(x_9, x_11, x_12, x_13);
lean_ctor_set(x_2, 0, x_14);
x_15 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_2, x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_20 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instToSnapshotTreeHeaderParsedSnapshot___lambda__1), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = 1;
x_23 = l_Lean_Language_SnapshotTask_map___rarg(x_18, x_20, x_21, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_pushOpt___rarg(x_24, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_SnapshotTask_pure___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2;
x_8 = 1;
x_9 = l_Lean_Language_SnapshotTask_map___rarg(x_5, x_7, x_6, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instMonadLiftLeanProcessingMLeanProcessingTIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Language_Lean_instMonadLiftProcessingTLeanProcessingT___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_CancelToken_new(x_5);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_apply_2(x_1, x_10, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = l_String_firstDiffPos(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
lean_ctor_set(x_2, 0, x_22);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_18);
x_24 = lean_apply_2(x_1, x_23, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = l_String_firstDiffPos(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_26);
x_33 = lean_apply_2(x_1, x_32, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_LeanProcessingM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_Lean_LeanProcessingM_run___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_nat_dec_lt(x_1, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_isBeforeEditPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_Lean_isBeforeEditPos(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_io_error_to_string(x_10);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lean_Language_diagnosticsOfHeaderError(x_12, x_13, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_apply_1(x_1, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = lean_apply_1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___rarg), 4, 0);
return x_2;
}
}
static uint32_t _init_l_Lean_Language_Lean_SetupImportsResult_trustLevel___default() {
_start:
{
uint32_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_withStdout___at_Lean_Language_Lean_process_doElab___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_set_stdout(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdout(x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_get_set_stdout(x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStdin___at_Lean_Language_Lean_process_doElab___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_set_stdin(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stdin(x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_get_set_stdin(x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_withStderr___at_Lean_Language_Lean_process_doElab___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_set_stderr(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_get_set_stderr(x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_get_set_stderr(x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__2;
x_2 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__3;
x_3 = lean_unsigned_to_nat(92u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__1;
x_5 = lean_st_mk_ref(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_mk_ref(x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_IO_FS_Stream_ofBuffer(x_6);
lean_inc(x_9);
x_12 = l_IO_FS_Stream_ofBuffer(x_9);
if (x_2 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Language_Lean_process_doElab___spec__2), 3, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
x_14 = l_IO_withStdin___at_Lean_Language_Lean_process_doElab___spec__3(x_11, x_13, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_9, x_16);
lean_dec(x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_string_validate_utf8(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_22 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5;
x_23 = l_panic___at_String_fromUTF8_x21___spec__1(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_string_from_utf8_unchecked(x_20);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_string_validate_utf8(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
x_31 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5;
x_32 = l_panic___at_String_fromUTF8_x21___spec__1(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_15);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_string_from_utf8_unchecked(x_29);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_15);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_15);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_12);
x_46 = lean_alloc_closure((void*)(l_IO_withStderr___at_Lean_Language_Lean_process_doElab___spec__4), 3, 2);
lean_closure_set(x_46, 0, x_12);
lean_closure_set(x_46, 1, x_1);
x_47 = lean_alloc_closure((void*)(l_IO_withStdout___at_Lean_Language_Lean_process_doElab___spec__2), 3, 2);
lean_closure_set(x_47, 0, x_12);
lean_closure_set(x_47, 1, x_46);
x_48 = l_IO_withStdin___at_Lean_Language_Lean_process_doElab___spec__3(x_11, x_47, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_9, x_50);
lean_dec(x_9);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_string_validate_utf8(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
x_56 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5;
x_57 = l_panic___at_String_fromUTF8_x21___spec__1(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_51, 0, x_58);
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_string_from_utf8_unchecked(x_54);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_49);
lean_ctor_set(x_51, 0, x_60);
return x_51;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_string_validate_utf8(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_65 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5;
x_66 = l_panic___at_String_fromUTF8_x21___spec__1(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_49);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_string_from_utf8_unchecked(x_63);
lean_dec(x_63);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_49);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_49);
x_72 = !lean_is_exclusive(x_51);
if (x_72 == 0)
{
return x_51;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_51, 0);
x_74 = lean_ctor_get(x_51, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_51);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_9);
x_76 = !lean_is_exclusive(x_48);
if (x_76 == 0)
{
return x_48;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_48, 0);
x_78 = lean_ctor_get(x_48, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_48);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_8);
if (x_80 == 0)
{
return x_8;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_8, 0);
x_82 = lean_ctor_get(x_8, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_8);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_5);
if (x_84 == 0)
{
return x_5;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_5, 0);
x_86 = lean_ctor_get(x_5, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_5);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getResetInfoTrees___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__3___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_Elab_Command_elabCommandTopLevel(x_2, x_8, x_3, x_4, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Lean_process_doElab___lambda__2___closed__1;
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Language_Lean_process_doElab___lambda__2___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Language_Lean_process_doElab___lambda__2___closed__3;
x_3 = l_Lean_NameSet_empty;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 6);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 7);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_4);
x_14 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_8);
lean_ctor_set(x_14, 3, x_9);
lean_ctor_set(x_14, 4, x_10);
lean_ctor_set(x_14, 5, x_11);
lean_ctor_set(x_14, 6, x_12);
lean_ctor_set(x_14, 7, x_13);
x_15 = l_Lean_Language_Lean_process_doElab___lambda__2___closed__4;
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_17 = 0;
lean_inc(x_2);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = l_Lean_Language_Snapshot_Diagnostics_empty;
lean_inc(x_2);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_17);
x_21 = l_Lean_Language_instTypeNameSnapshotLeaf;
x_22 = l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1(x_21, x_20);
x_23 = lean_task_pure(x_22);
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
lean_inc(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_task_pure(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_io_promise_resolve(x_29, x_30, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_4, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
x_40 = l_Lean_Elab_instInhabitedInfoTree;
x_41 = l_outOfBounds___rarg(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_17);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_14);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = l_Lean_Elab_instInhabitedInfoTree;
x_46 = l_Lean_PersistentArray_get_x21___rarg(x_45, x_36, x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_17);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_14);
lean_ctor_set(x_33, 0, x_49);
return x_33;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_lt(x_54, x_53);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_52);
x_56 = l_Lean_Elab_instInhabitedInfoTree;
x_57 = l_outOfBounds___rarg(x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_17);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_14);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = l_Lean_Elab_instInhabitedInfoTree;
x_63 = l_Lean_PersistentArray_get_x21___rarg(x_62, x_52, x_54);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_17);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_14);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_51);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_14);
lean_dec(x_12);
x_68 = !lean_is_exclusive(x_33);
if (x_68 == 0)
{
return x_33;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_33, 0);
x_70 = lean_ctor_get(x_33, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_33);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_31);
if (x_72 == 0)
{
return x_31;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_31, 0);
x_74 = lean_ctor_get(x_31, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_31);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Lean_stderrAsMessages;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_st_ref_get(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_mk_ref(x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_firstFrontendMacroScope;
x_25 = lean_box(0);
x_26 = 0;
lean_inc(x_3);
lean_inc(x_17);
lean_inc(x_16);
x_27 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_3);
lean_ctor_set(x_27, 4, x_18);
lean_ctor_set(x_27, 5, x_24);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_19);
lean_ctor_set(x_27, 8, x_20);
lean_ctor_set(x_27, 9, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*10, x_26);
lean_inc(x_4);
x_28 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_doElab___lambda__1), 5, 2);
lean_closure_set(x_28, 0, x_4);
lean_closure_set(x_28, 1, x_5);
lean_inc(x_7);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withLoggingExceptions), 4, 3);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_7);
x_30 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_ctor_get(x_6, 1);
x_32 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__1;
x_33 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_31, x_32);
x_34 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1(x_30, x_33, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_dec(x_39);
x_40 = lean_st_ref_get(x_13, x_36);
lean_dec(x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_take(x_1, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
lean_ctor_set(x_35, 1, x_46);
lean_ctor_set(x_35, 0, x_43);
x_47 = lean_st_ref_set(x_1, x_35, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_7, x_48);
lean_dec(x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
x_53 = l_String_isEmpty(x_38);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = l_Lean_FileMap_toPosition(x_17, x_3);
lean_dec(x_3);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_38);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = 0;
x_58 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__4;
x_59 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_59, 0, x_16);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_20);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*5, x_26);
lean_ctor_set_uint8(x_59, sizeof(void*)*5 + 1, x_57);
x_60 = l_Lean_MessageLog_add(x_59, x_52);
x_61 = lean_box(0);
x_62 = l_Lean_Language_Lean_process_doElab___lambda__2(x_50, x_20, x_4, x_60, x_61, x_51);
lean_dec(x_4);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
x_63 = lean_box(0);
x_64 = l_Lean_Language_Lean_process_doElab___lambda__2(x_50, x_20, x_4, x_52, x_63, x_51);
lean_dec(x_4);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
return x_47;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_43);
lean_free_object(x_35);
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_44);
if (x_73 == 0)
{
return x_44;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_44, 0);
x_75 = lean_ctor_get(x_44, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_44);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_free_object(x_35);
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_40);
if (x_77 == 0)
{
return x_40;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_40, 0);
x_79 = lean_ctor_get(x_40, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_40);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_35, 0);
lean_inc(x_81);
lean_dec(x_35);
x_82 = lean_st_ref_get(x_13, x_36);
lean_dec(x_13);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_take(x_1, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_st_ref_set(x_1, x_89, x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_get(x_7, x_91);
lean_dec(x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
x_96 = l_String_isEmpty(x_81);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = l_Lean_FileMap_toPosition(x_17, x_3);
lean_dec(x_3);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_81);
x_99 = l_Lean_MessageData_ofFormat(x_98);
x_100 = 0;
x_101 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__4;
x_102 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_102, 0, x_16);
lean_ctor_set(x_102, 1, x_97);
lean_ctor_set(x_102, 2, x_20);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*5, x_26);
lean_ctor_set_uint8(x_102, sizeof(void*)*5 + 1, x_100);
x_103 = l_Lean_MessageLog_add(x_102, x_95);
x_104 = lean_box(0);
x_105 = l_Lean_Language_Lean_process_doElab___lambda__2(x_93, x_20, x_4, x_103, x_104, x_94);
lean_dec(x_4);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
x_106 = lean_box(0);
x_107 = l_Lean_Language_Lean_process_doElab___lambda__2(x_93, x_20, x_4, x_95, x_106, x_94);
lean_dec(x_4);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_108 = lean_ctor_get(x_92, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_110 = x_92;
} else {
 lean_dec_ref(x_92);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_90, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_90, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_114 = x_90;
} else {
 lean_dec_ref(x_90);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_86, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_86, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_118 = x_86;
} else {
 lean_dec_ref(x_86);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_82, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_82, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_122 = x_82;
} else {
 lean_dec_ref(x_82);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_34);
if (x_124 == 0)
{
return x_34;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_34, 0);
x_126 = lean_ctor_get(x_34, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_34);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_12);
if (x_128 == 0)
{
return x_12;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_12, 0);
x_130 = lean_ctor_get(x_12, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_12);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_9);
if (x_132 == 0)
{
return x_9;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_9, 0);
x_134 = lean_ctor_get(x_9, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_9);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_8 = 0;
x_9 = l_Lean_Syntax_getTailPos_x3f(x_1, x_8);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = l_Lean_Elab_Command_instInhabitedScope;
x_14 = l_List_head_x21___rarg(x_13, x_11);
x_15 = l_Lean_MessageLog_empty;
lean_ctor_set(x_2, 1, x_15);
x_16 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 1);
lean_closure_set(x_16, 0, x_2);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_doElab___lambda__3___boxed), 8, 6);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_1);
lean_closure_set(x_17, 5, x_14);
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_20, x_18, x_7);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_9, 0, x_24);
x_25 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_9, x_18, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_28, x_18, x_7);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_ctor_get(x_2, 4);
x_34 = lean_ctor_get(x_2, 5);
x_35 = lean_ctor_get(x_2, 6);
x_36 = lean_ctor_get(x_2, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_37 = l_Lean_Elab_Command_instInhabitedScope;
x_38 = l_List_head_x21___rarg(x_37, x_31);
x_39 = l_Lean_MessageLog_empty;
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_31);
lean_ctor_set(x_40, 3, x_32);
lean_ctor_set(x_40, 4, x_33);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_36);
x_41 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 1);
lean_closure_set(x_41, 0, x_40);
lean_inc(x_3);
x_42 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_doElab___lambda__3___boxed), 8, 6);
lean_closure_set(x_42, 0, x_5);
lean_closure_set(x_42, 1, x_6);
lean_closure_set(x_42, 2, x_3);
lean_closure_set(x_42, 3, x_4);
lean_closure_set(x_42, 4, x_1);
lean_closure_set(x_42, 5, x_38);
x_43 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_42);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc(x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_3);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_45, x_43, x_7);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_47 = lean_ctor_get(x_9, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_48 = x_9;
} else {
 lean_dec_ref(x_9);
 x_48 = lean_box(0);
}
lean_inc(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_47);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_50, x_43, x_7);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Language_Lean_process_doElab___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_doElab___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Language_Lean_process_doElab___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = l_Lean_Syntax_getRange_x3f(x_2, x_13);
x_16 = lean_io_promise_result(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_18, 4, x_5);
lean_ctor_set(x_18, 5, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_box(0);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
x_25 = l_Lean_Syntax_getRange_x3f(x_2, x_23);
x_26 = lean_io_promise_result(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_4);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_5);
lean_ctor_set(x_28, 5, x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_Language_Lean_process_parseCmd(x_5, x_1, x_6, x_2, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_io_promise_new(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1;
x_61 = lean_st_mk_ref(x_60, x_12);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_13 = x_62;
x_14 = x_63;
goto block_59;
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_7, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 5);
lean_inc(x_70);
lean_dec(x_69);
x_13 = x_70;
x_14 = x_12;
goto block_59;
}
block_59:
{
lean_object* x_15; 
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_40; 
x_40 = lean_box(0);
x_15 = x_40;
goto block_39;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 3);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_42, 1, x_47);
lean_ctor_set(x_42, 0, x_46);
x_15 = x_7;
goto block_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 3);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_7, 0, x_51);
x_15 = x_7;
goto block_39;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_7, 0);
lean_inc(x_52);
lean_dec(x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 3);
lean_inc(x_56);
lean_dec(x_53);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_15 = x_58;
goto block_39;
}
}
block_39:
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_inc(x_4);
lean_inc(x_13);
lean_inc(x_1);
x_17 = l_Lean_Language_Lean_process_doElab(x_1, x_2, x_3, x_16, x_13, x_4, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l_Lean_Parser_isTerminalCommand(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_inc(x_6);
x_21 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__2), 4, 2);
lean_closure_set(x_21, 0, x_6);
lean_closure_set(x_21, 1, x_4);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = 1;
lean_inc(x_18);
x_24 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_18, x_21, x_22, x_23, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = l_Lean_Language_Lean_process_parseCmd___lambda__1(x_5, x_1, x_11, x_6, x_18, x_13, x_27, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = l_Lean_Language_Lean_process_parseCmd___lambda__1(x_5, x_1, x_11, x_6, x_18, x_13, x_33, x_19);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
return x_10;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_10);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_apply_2(x_2, x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_st_ref_set(x_8, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Language_Lean_process_parseCmd(x_6, x_2, x_7, x_3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__5), 5, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = 1;
x_9 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_3, x_6, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
if (x_6 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = l_Lean_Language_Lean_process_parseCmd___lambda__4(x_1, x_2, x_8, x_7);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = l_Lean_Syntax_structEq(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = l_Lean_Language_Lean_process_parseCmd___lambda__4(x_1, x_2, x_14, x_7);
lean_dec(x_1);
return x_15;
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__6), 5, 3);
lean_closure_set(x_22, 0, x_5);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_21);
x_23 = lean_ctor_get(x_10, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = 1;
x_26 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_23, x_22, x_24, x_25, x_7);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_11, 0, x_28);
lean_ctor_set(x_26, 0, x_3);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_11, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_11);
lean_free_object(x_3);
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__6), 5, 3);
lean_closure_set(x_37, 0, x_5);
lean_closure_set(x_37, 1, x_1);
lean_closure_set(x_37, 2, x_36);
x_38 = lean_ctor_get(x_10, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = 1;
x_41 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_38, x_37, x_39, x_40, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_3, 1, x_45);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_3);
lean_dec(x_10);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_3);
x_51 = lean_ctor_get(x_11, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_52 = x_11;
} else {
 lean_dec_ref(x_11);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__6), 5, 3);
lean_closure_set(x_53, 0, x_5);
lean_closure_set(x_53, 1, x_1);
lean_closure_set(x_53, 2, x_51);
x_54 = lean_ctor_get(x_10, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = 1;
x_57 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_54, x_53, x_55, x_56, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_10);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___lambda__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_string_utf8_byte_size(x_10);
lean_dec(x_10);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
x_16 = l_Lean_Elab_Command_instInhabitedScope;
x_17 = l_List_head_x21___rarg(x_16, x_15);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_Lean_MessageLog_empty;
x_23 = l_Lean_Parser_parseCommand(x_9, x_21, x_1, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_4);
lean_inc(x_26);
lean_inc(x_2);
lean_inc(x_25);
x_28 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__3___boxed), 9, 7);
lean_closure_set(x_28, 0, x_25);
lean_closure_set(x_28, 1, x_3);
lean_closure_set(x_28, 2, x_8);
lean_closure_set(x_28, 3, x_2);
lean_closure_set(x_28, 4, x_27);
lean_closure_set(x_28, 5, x_26);
lean_closure_set(x_28, 6, x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
x_29 = l_Lean_Language_Lean_process_parseCmd___lambda__8___closed__1;
x_30 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_28);
x_31 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_13, x_30, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_inc(x_2);
x_34 = lean_alloc_closure((void*)(l_Lean_Language_Lean_isBeforeEditPos___boxed), 3, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_2);
x_35 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__7___boxed), 7, 5);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_28);
lean_closure_set(x_35, 2, x_32);
lean_closure_set(x_35, 3, x_25);
lean_closure_set(x_35, 4, x_26);
x_36 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
x_37 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_13, x_36, x_7);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_12, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_15);
x_16 = l_Lean_Language_SnapshotTask_get_x3f___rarg(x_15, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_19, x_6, x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 2);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Language_Lean_isBeforeEditPos(x_28, x_6, x_23);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_15);
lean_dec(x_14);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_33, x_6, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_14, 2);
lean_inc(x_36);
x_37 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__6), 5, 3);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_15);
x_38 = lean_ctor_get(x_14, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = 1;
x_41 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_38, x_37, x_39, x_40, x_35);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_ctor_set(x_17, 0, x_43);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 0, x_14);
x_44 = l_Lean_Language_SnapshotTask_pure___rarg(x_22);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
lean_ctor_set(x_17, 0, x_45);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 0, x_14);
x_47 = l_Lean_Language_SnapshotTask_pure___rarg(x_22);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_free_object(x_22);
lean_free_object(x_17);
lean_dec(x_14);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
lean_dec(x_22);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Language_Lean_isBeforeEditPos(x_55, x_6, x_23);
lean_dec(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_17);
lean_dec(x_15);
lean_dec(x_14);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_box(0);
x_61 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_60, x_6, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_ctor_get(x_14, 2);
lean_inc(x_63);
x_64 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__6), 5, 3);
lean_closure_set(x_64, 0, x_63);
lean_closure_set(x_64, 1, x_2);
lean_closure_set(x_64, 2, x_15);
x_65 = lean_ctor_get(x_14, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = 1;
x_68 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_65, x_64, x_66, x_67, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
lean_ctor_set(x_17, 0, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_14);
lean_ctor_set(x_72, 1, x_17);
x_73 = l_Lean_Language_SnapshotTask_pure___rarg(x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_17);
lean_dec(x_14);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_17, 0);
lean_inc(x_79);
lean_dec(x_17);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_dec(x_16);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_81, 2);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Language_Lean_isBeforeEditPos(x_84, x_6, x_80);
lean_dec(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_15);
lean_dec(x_14);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_box(0);
x_90 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_89, x_6, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_ctor_get(x_14, 2);
lean_inc(x_92);
x_93 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd___lambda__6), 5, 3);
lean_closure_set(x_93, 0, x_92);
lean_closure_set(x_93, 1, x_2);
lean_closure_set(x_93, 2, x_15);
x_94 = lean_ctor_get(x_14, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = 1;
x_97 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_94, x_93, x_95, x_96, x_91);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_98);
if (lean_is_scalar(x_82)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_82;
}
lean_ctor_set(x_102, 0, x_14);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Language_SnapshotTask_pure___rarg(x_102);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_82);
lean_dec(x_14);
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_16);
if (x_109 == 0)
{
return x_16;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_16, 0);
x_111 = lean_ctor_get(x_16, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_16);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_doElab___lambda__2___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_parseCmd___closed__2;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_instTypeNameSnapshotLeaf;
x_2 = l_Lean_Language_Lean_process_parseCmd___closed__1;
x_3 = l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_process_parseCmd___closed__4;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_parseCmd___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Lean_process_parseCmd___closed__3;
x_2 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_process_parseCmd___closed__7;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_parseCmd___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Lean_process_parseCmd___closed__3;
x_2 = l_Lean_Language_Lean_process_parseCmd___closed__6;
x_3 = l_Lean_Language_Lean_process_parseCmd___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_process_parseCmd___closed__10;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_parseCmd___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_parseCmd___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_st_ref_get(x_6, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
lean_inc(x_4);
x_12 = l_Lean_Language_Lean_process_parseCmd___lambda__9(x_2, x_4, x_3, x_1, x_11, x_4, x_10);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1;
x_15 = lean_st_mk_ref(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
x_19 = l_Lean_Language_Lean_process_parseCmd___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = l_Lean_Language_SnapshotTask_pure___rarg(x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Language_Lean_process_parseCmd___closed__12;
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
x_26 = l_Lean_Language_SnapshotTask_pure___rarg(x_25);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_box(0);
x_30 = l_Lean_Language_Lean_process_parseCmd___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_32 = l_Lean_Language_SnapshotTask_pure___rarg(x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Language_Lean_process_parseCmd___closed__12;
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
x_37 = l_Lean_Language_SnapshotTask_pure___rarg(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Language_Lean_process_parseCmd___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_Lean_process_parseCmd___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_Language_Lean_process_parseCmd___lambda__7(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Language_Lean_process_parseCmd___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseCmd___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Language_Lean_process_parseCmd___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
static lean_object* _init_l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1;
x_2 = l_Array_toPArray_x27___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1(x_5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_3(x_1, x_2, x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_import", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__5;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_environment_set_main_module(x_2, x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_14 = l_Lean_Elab_Command_mkState(x_13, x_3, x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_16 = lean_ctor_get(x_14, 6);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 3);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2;
x_22 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_4, x_21);
lean_dec(x_4);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_box(0);
x_25 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3;
x_26 = lean_box(0);
x_27 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6;
lean_inc(x_23);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8;
lean_inc(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_6, x_33);
lean_dec(x_6);
x_35 = l_Lean_Syntax_getArgs(x_34);
lean_dec(x_34);
x_36 = lean_array_to_list(lean_box(0), x_35);
x_37 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1(x_36);
x_38 = l_List_toPArray_x27___rarg(x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9;
x_42 = lean_array_push(x_41, x_40);
x_43 = l_Array_toPArray_x27___rarg(x_42);
lean_dec(x_42);
x_44 = 1;
x_45 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
lean_inc(x_43);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
x_47 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1;
lean_ctor_set(x_14, 6, x_46);
lean_ctor_set(x_14, 4, x_22);
lean_ctor_set(x_14, 3, x_47);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 0, x_13);
x_48 = lean_box(0);
lean_inc(x_14);
x_49 = l_Lean_Language_Lean_process_parseCmd(x_48, x_7, x_14, x_10, x_11);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_lt(x_53, x_52);
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_14);
lean_ctor_set(x_55, 1, x_51);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
if (x_54 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_43);
x_57 = l_Lean_Elab_instInhabitedInfoTree;
x_58 = l_outOfBounds___rarg(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = 0;
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_49, 0, x_62);
return x_49;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_63 = l_Lean_Elab_instInhabitedInfoTree;
x_64 = l_Lean_PersistentArray_get_x21___rarg(x_63, x_43, x_53);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = 0;
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_8);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_56);
lean_ctor_set(x_49, 0, x_68);
return x_49;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_49, 0);
x_70 = lean_ctor_get(x_49, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_49);
x_71 = lean_ctor_get(x_43, 2);
lean_inc(x_71);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_71);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_69);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
if (x_73 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_43);
x_76 = l_Lean_Elab_instInhabitedInfoTree;
x_77 = l_outOfBounds___rarg(x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = 0;
x_80 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_80, 0, x_8);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_70);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = l_Lean_Elab_instInhabitedInfoTree;
x_84 = l_Lean_PersistentArray_get_x21___rarg(x_83, x_43, x_72);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = 0;
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_8);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_75);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_70);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_90 = lean_ctor_get(x_14, 2);
x_91 = lean_ctor_get(x_14, 5);
x_92 = lean_ctor_get(x_14, 7);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_14);
x_93 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2;
x_94 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_4, x_93);
lean_dec(x_4);
x_95 = lean_ctor_get(x_5, 2);
x_96 = lean_box(0);
x_97 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3;
x_98 = lean_box(0);
x_99 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6;
lean_inc(x_95);
lean_inc(x_13);
x_100 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_100, 0, x_13);
lean_ctor_set(x_100, 1, x_95);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_96);
lean_ctor_set(x_100, 4, x_98);
lean_ctor_set(x_100, 5, x_96);
lean_ctor_set(x_100, 6, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8;
lean_inc(x_6);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_6);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = l_Lean_Syntax_getArg(x_6, x_105);
lean_dec(x_6);
x_107 = l_Lean_Syntax_getArgs(x_106);
lean_dec(x_106);
x_108 = lean_array_to_list(lean_box(0), x_107);
x_109 = l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1(x_108);
x_110 = l_List_toPArray_x27___rarg(x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9;
x_114 = lean_array_push(x_113, x_112);
x_115 = l_Array_toPArray_x27___rarg(x_114);
lean_dec(x_114);
x_116 = 1;
x_117 = l_Lean_Language_Lean_process_doElab___lambda__3___closed__3;
lean_inc(x_115);
x_118 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_116);
x_119 = l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1;
x_120 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_120, 0, x_13);
lean_ctor_set(x_120, 1, x_3);
lean_ctor_set(x_120, 2, x_90);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_94);
lean_ctor_set(x_120, 5, x_91);
lean_ctor_set(x_120, 6, x_118);
lean_ctor_set(x_120, 7, x_92);
x_121 = lean_box(0);
lean_inc(x_120);
x_122 = l_Lean_Language_Lean_process_parseCmd(x_121, x_7, x_120, x_10, x_11);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_115, 2);
lean_inc(x_126);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_nat_dec_lt(x_127, x_126);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_120);
lean_ctor_set(x_129, 1, x_123);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (x_128 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_115);
x_131 = l_Lean_Elab_instInhabitedInfoTree;
x_132 = l_outOfBounds___rarg(x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = 0;
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_8);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_130);
if (lean_is_scalar(x_125)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_125;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_124);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = l_Lean_Elab_instInhabitedInfoTree;
x_139 = l_Lean_PersistentArray_get_x21___rarg(x_138, x_115, x_127);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = 0;
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_8);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
if (lean_is_scalar(x_125)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_125;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_124);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint32(x_4, sizeof(void*)*2);
x_9 = l_Lean_MessageLog_empty;
x_10 = 1;
lean_inc(x_2);
lean_inc(x_7);
x_11 = l_Lean_Elab_processHeader(x_1, x_7, x_9, x_2, x_8, x_10, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_16, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_MessageLog_hasErrors(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_17);
lean_free_object(x_12);
x_22 = lean_box(0);
x_23 = l_Lean_Language_Lean_process_processHeader___lambda__3(x_4, x_15, x_16, x_7, x_2, x_1, x_3, x_19, x_22, x_5, x_20);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_10);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_25);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = l_Lean_MessageLog_hasErrors(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_12);
x_29 = lean_box(0);
x_30 = l_Lean_Language_Lean_process_processHeader___lambda__3(x_4, x_15, x_16, x_7, x_2, x_1, x_3, x_26, x_29, x_5, x_27);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_10);
lean_ctor_set(x_12, 1, x_31);
lean_ctor_set(x_12, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
lean_inc(x_35);
x_36 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_35, x_13);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = l_Lean_MessageLog_hasErrors(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = l_Lean_Language_Lean_process_processHeader___lambda__3(x_4, x_34, x_35, x_7, x_2, x_1, x_3, x_37, x_41, x_5, x_38);
lean_dec(x_2);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_10);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
if (lean_is_scalar(x_39)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_39;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_11);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Lean_Language_Lean_process_processHeader___lambda__4(x_1, x_2, x_3, x_9, x_5, x_6);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Language_Lean_process_processHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_processHeader___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_string_utf8_byte_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_processHeader___lambda__2), 4, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_processHeader___lambda__5), 6, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_3);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2___rarg), 4, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Language_Lean_process_processHeader___closed__1;
x_16 = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___rarg), 4, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_4);
x_17 = l_Lean_Language_SnapshotTask_ofIO___rarg(x_11, x_16, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_processHeader___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Language_Lean_process_processHeader___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_parseHeader(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Language_Lean_process_processHeader(x_2, x_3, x_4, x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
lean_ctor_set(x_10, 1, x_16);
lean_ctor_set(x_10, 0, x_4);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_10);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_box(0);
lean_ctor_set(x_10, 1, x_24);
lean_ctor_set(x_10, 0, x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_10);
x_28 = 0;
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_28);
x_30 = lean_ctor_get(x_5, 3);
lean_inc(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_Language_Lean_process_processHeader(x_2, x_3, x_4, x_8, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = 0;
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_43);
x_45 = lean_ctor_get(x_5, 3);
lean_inc(x_45);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_6);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_46);
if (lean_is_scalar(x_39)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_39;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_7, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_st_ref_set(x_9, x_11, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_3(x_2, x_13, x_4, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
x_9 = l_Lean_Language_Lean_process_parseCmd(x_7, x_2, x_8, x_3, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Language_SnapshotTask_pure___rarg(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Language_SnapshotTask_pure___rarg(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
x_6 = l_Lean_Language_SnapshotTask_pure___rarg(x_3);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__5), 6, 4);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = 1;
x_17 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_13, x_14, x_15, x_16, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Language_Lean_process_parseHeader___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_9, x_10);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__3___boxed), 9, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = l_Lean_Language_Lean_isBeforeEditPos(x_16, x_9, x_10);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_7);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Language_Lean_process_parseHeader___lambda__4(x_5, x_15, x_21, x_9, x_20);
lean_dec(x_5);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 3);
lean_inc(x_28);
lean_inc(x_27);
x_29 = l_Lean_Syntax_structEq(x_27, x_3);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_17);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = l_Lean_Language_Lean_process_parseHeader___lambda__4(x_5, x_15, x_30, x_9, x_24);
lean_dec(x_5);
return x_31;
}
else
{
lean_dec(x_15);
lean_dec(x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
uint8_t x_32; 
lean_free_object(x_17);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_14, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_14, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_14, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_14, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_14, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_5);
x_42 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_42, 0, x_4);
lean_closure_set(x_42, 1, x_5);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = 1;
x_45 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_41, x_42, x_43, x_44, x_24);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_39, 1, x_48);
x_51 = 0;
lean_ctor_set(x_26, 1, x_50);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_51);
x_52 = lean_ctor_get(x_5, 3);
lean_inc(x_52);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_52);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_45, 0, x_14);
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
lean_dec(x_26);
x_55 = lean_box(0);
lean_ctor_set(x_39, 1, x_53);
x_56 = 0;
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_56);
x_58 = lean_ctor_get(x_5, 3);
lean_inc(x_58);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_58);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 0, x_57);
lean_ctor_set(x_45, 0, x_14);
return x_45;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_ctor_get(x_26, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_62 = x_26;
} else {
 lean_dec_ref(x_26);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
lean_ctor_set(x_39, 1, x_59);
x_64 = 0;
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_64);
x_66 = lean_ctor_get(x_5, 3);
lean_inc(x_66);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_66);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_14);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_68 = lean_ctor_get(x_39, 0);
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_39);
lean_inc(x_5);
x_70 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_70, 0, x_4);
lean_closure_set(x_70, 1, x_5);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = 1;
x_73 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_69, x_70, x_71, x_72, x_24);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_26, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_78 = x_26;
} else {
 lean_dec_ref(x_26);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_28, 0, x_80);
x_81 = 0;
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 2, 1);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_81);
x_83 = lean_ctor_get(x_5, 3);
lean_inc(x_83);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_83);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 0, x_82);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_14);
lean_ctor_set(x_84, 1, x_75);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_85 = lean_ctor_get(x_28, 0);
lean_inc(x_85);
lean_dec(x_28);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
lean_inc(x_5);
x_89 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_89, 0, x_4);
lean_closure_set(x_89, 1, x_5);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = 1;
x_92 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_87, x_89, x_90, x_91, x_24);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_26, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_97 = x_26;
} else {
 lean_dec_ref(x_26);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_93);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = 0;
if (lean_is_scalar(x_97)) {
 x_102 = lean_alloc_ctor(0, 2, 1);
} else {
 x_102 = x_97;
}
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_101);
x_103 = lean_ctor_get(x_5, 3);
lean_inc(x_103);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_103);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 3, x_100);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 0, x_102);
if (lean_is_scalar(x_95)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_95;
}
lean_ctor_set(x_104, 0, x_14);
lean_ctor_set(x_104, 1, x_94);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_14);
x_105 = lean_ctor_get(x_28, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_106 = x_28;
} else {
 lean_dec_ref(x_28);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
lean_inc(x_5);
x_110 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_110, 0, x_4);
lean_closure_set(x_110, 1, x_5);
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
x_112 = 1;
x_113 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_108, x_110, x_111, x_112, x_24);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_26, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_118 = x_26;
} else {
 lean_dec_ref(x_26);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_109;
}
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set(x_120, 1, x_114);
if (lean_is_scalar(x_106)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_106;
}
lean_ctor_set(x_121, 0, x_120);
x_122 = 0;
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 1);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_119);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_122);
x_124 = lean_ctor_get(x_5, 3);
lean_inc(x_124);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_124);
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_6);
lean_ctor_set(x_125, 2, x_27);
lean_ctor_set(x_125, 3, x_121);
lean_ctor_set(x_125, 4, x_7);
if (lean_is_scalar(x_116)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_116;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_115);
return x_126;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_17, 1);
lean_inc(x_127);
lean_dec(x_17);
x_128 = lean_ctor_get(x_14, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_14, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_14, 3);
lean_inc(x_130);
lean_inc(x_129);
x_131 = l_Lean_Syntax_structEq(x_129, x_3);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
x_132 = lean_box(0);
x_133 = l_Lean_Language_Lean_process_parseHeader___lambda__4(x_5, x_15, x_132, x_9, x_127);
lean_dec(x_5);
return x_133;
}
else
{
lean_dec(x_15);
lean_dec(x_9);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_134; 
lean_dec(x_129);
lean_dec(x_128);
lean_free_object(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_14);
lean_ctor_set(x_134, 1, x_127);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_135 = x_14;
} else {
 lean_dec_ref(x_14);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
lean_inc(x_5);
x_141 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_141, 0, x_4);
lean_closure_set(x_141, 1, x_5);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = 1;
x_144 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_139, x_141, x_142, x_143, x_127);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_128, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_149 = x_128;
} else {
 lean_dec_ref(x_128);
 x_149 = lean_box(0);
}
x_150 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_140;
}
lean_ctor_set(x_151, 0, x_138);
lean_ctor_set(x_151, 1, x_145);
if (lean_is_scalar(x_137)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_137;
}
lean_ctor_set(x_152, 0, x_151);
x_153 = 0;
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(0, 2, 1);
} else {
 x_154 = x_149;
}
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_150);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_153);
x_155 = lean_ctor_get(x_5, 3);
lean_inc(x_155);
lean_dec(x_5);
lean_ctor_set(x_7, 0, x_155);
if (lean_is_scalar(x_135)) {
 x_156 = lean_alloc_ctor(0, 5, 0);
} else {
 x_156 = x_135;
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_6);
lean_ctor_set(x_156, 2, x_129);
lean_ctor_set(x_156, 3, x_152);
lean_ctor_set(x_156, 4, x_7);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_146);
return x_157;
}
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_7, 0);
lean_inc(x_158);
lean_dec(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_159 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__3___boxed), 9, 6);
lean_closure_set(x_159, 0, x_1);
lean_closure_set(x_159, 1, x_2);
lean_closure_set(x_159, 2, x_3);
lean_closure_set(x_159, 3, x_4);
lean_closure_set(x_159, 4, x_5);
lean_closure_set(x_159, 5, x_6);
x_160 = lean_ctor_get(x_4, 0);
lean_inc(x_160);
x_161 = l_Lean_Language_Lean_isBeforeEditPos(x_160, x_9, x_10);
lean_dec(x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_box(0);
x_166 = l_Lean_Language_Lean_process_parseHeader___lambda__4(x_5, x_159, x_165, x_9, x_164);
lean_dec(x_5);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_158, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_158, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_158, 3);
lean_inc(x_171);
lean_inc(x_170);
x_172 = l_Lean_Syntax_structEq(x_170, x_3);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_158);
lean_dec(x_6);
lean_dec(x_4);
x_173 = lean_box(0);
x_174 = l_Lean_Language_Lean_process_parseHeader___lambda__4(x_5, x_159, x_173, x_9, x_167);
lean_dec(x_5);
return x_174;
}
else
{
lean_dec(x_159);
lean_dec(x_9);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_175; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_168)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_168;
}
lean_ctor_set(x_175, 0, x_158);
lean_ctor_set(x_175, 1, x_167);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_168);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_176 = x_158;
} else {
 lean_dec_ref(x_158);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_178 = x_171;
} else {
 lean_dec_ref(x_171);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_181 = x_177;
} else {
 lean_dec_ref(x_177);
 x_181 = lean_box(0);
}
lean_inc(x_5);
x_182 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_182, 0, x_4);
lean_closure_set(x_182, 1, x_5);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = 1;
x_185 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_180, x_182, x_183, x_184, x_167);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_169, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_190 = x_169;
} else {
 lean_dec_ref(x_169);
 x_190 = lean_box(0);
}
x_191 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_179);
lean_ctor_set(x_192, 1, x_186);
if (lean_is_scalar(x_178)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_178;
}
lean_ctor_set(x_193, 0, x_192);
x_194 = 0;
if (lean_is_scalar(x_190)) {
 x_195 = lean_alloc_ctor(0, 2, 1);
} else {
 x_195 = x_190;
}
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_191);
lean_ctor_set_uint8(x_195, sizeof(void*)*2, x_194);
x_196 = lean_ctor_get(x_5, 3);
lean_inc(x_196);
lean_dec(x_5);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
if (lean_is_scalar(x_176)) {
 x_198 = lean_alloc_ctor(0, 5, 0);
} else {
 x_198 = x_176;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_6);
lean_ctor_set(x_198, 2, x_170);
lean_ctor_set(x_198, 3, x_193);
lean_ctor_set(x_198, 4, x_197);
if (lean_is_scalar(x_188)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_188;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_187);
return x_199;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_MessageLog_hasErrors(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Language_Lean_process_parseHeader___lambda__7(x_11, x_1, x_9, x_10, x_2, x_3, x_4, x_13, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_11, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_box(0);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_25);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_9);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__2___boxed), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__8), 7, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_4);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Language_Lean_process_processHeader___spec__2___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l___private_Lean_Language_Lean_0__Lean_Language_Lean_withHeaderExceptions___rarg(x_8, x_11, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_box(0);
lean_inc(x_3);
x_7 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_5, x_1, x_3, x_2, x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_box(0);
lean_inc(x_3);
x_12 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_10, x_1, x_3, x_2, x_11, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
lean_inc(x_8);
x_17 = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(x_8);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_8, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_8, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
x_24 = l_Lean_Language_SnapshotTask_get_x3f___rarg(x_17, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
lean_inc(x_3);
x_28 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_27, x_3, x_26);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
lean_inc(x_3);
x_32 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_31, x_3, x_30);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Language_SnapshotTask_get_x3f___rarg(x_36, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
lean_inc(x_3);
x_41 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_40, x_3, x_39);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Language_Lean_isBeforeEditPos(x_47, x_3, x_44);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_38);
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
lean_inc(x_3);
x_53 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_52, x_3, x_51);
return x_53;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_16, 0);
x_57 = lean_ctor_get(x_16, 1);
lean_inc(x_3);
lean_inc(x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_58, 0, x_56);
lean_closure_set(x_58, 1, x_3);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = 1;
x_61 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_57, x_58, x_59, x_60, x_54);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_14);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = lean_ctor_get(x_14, 1);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_16, 1, x_64);
lean_ctor_set(x_38, 0, x_16);
x_67 = 0;
lean_ctor_set(x_14, 1, x_66);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_67);
x_68 = lean_ctor_get(x_3, 3);
lean_inc(x_68);
lean_dec(x_3);
lean_ctor_set(x_29, 0, x_68);
lean_ctor_set(x_8, 4, x_29);
lean_ctor_set(x_8, 3, x_38);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_61, 0, x_8);
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_14, 0);
lean_inc(x_70);
lean_dec(x_14);
x_71 = lean_box(0);
lean_ctor_set(x_16, 1, x_69);
lean_ctor_set(x_38, 0, x_16);
x_72 = 0;
x_73 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_72);
x_74 = lean_ctor_get(x_3, 3);
lean_inc(x_74);
lean_dec(x_3);
lean_ctor_set(x_29, 0, x_74);
lean_ctor_set(x_8, 4, x_29);
lean_ctor_set(x_8, 3, x_38);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_73);
lean_ctor_set(x_61, 0, x_8);
return x_61;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
x_77 = lean_ctor_get(x_14, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_78 = x_14;
} else {
 lean_dec_ref(x_14);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
lean_ctor_set(x_16, 1, x_75);
lean_ctor_set(x_38, 0, x_16);
x_80 = 0;
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 1);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_80);
x_82 = lean_ctor_get(x_3, 3);
lean_inc(x_82);
lean_dec(x_3);
lean_ctor_set(x_29, 0, x_82);
lean_ctor_set(x_8, 4, x_29);
lean_ctor_set(x_8, 3, x_38);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_8);
lean_ctor_set(x_83, 1, x_76);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_16);
lean_dec(x_56);
lean_free_object(x_38);
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
return x_61;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_61, 0);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_61);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_16, 0);
x_89 = lean_ctor_get(x_16, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_88);
x_90 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_3);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = 1;
x_93 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_89, x_90, x_91, x_92, x_54);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_14, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_98 = x_14;
} else {
 lean_dec_ref(x_14);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_94);
lean_ctor_set(x_38, 0, x_100);
x_101 = 0;
if (lean_is_scalar(x_98)) {
 x_102 = lean_alloc_ctor(0, 2, 1);
} else {
 x_102 = x_98;
}
lean_ctor_set(x_102, 0, x_97);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_101);
x_103 = lean_ctor_get(x_3, 3);
lean_inc(x_103);
lean_dec(x_3);
lean_ctor_set(x_29, 0, x_103);
lean_ctor_set(x_8, 4, x_29);
lean_ctor_set(x_8, 3, x_38);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_102);
if (lean_is_scalar(x_96)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_96;
}
lean_ctor_set(x_104, 0, x_8);
lean_ctor_set(x_104, 1, x_95);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
lean_free_object(x_38);
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_107 = x_93;
} else {
 lean_dec_ref(x_93);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_109 = lean_ctor_get(x_38, 0);
lean_inc(x_109);
lean_dec(x_38);
x_110 = lean_ctor_get(x_37, 1);
lean_inc(x_110);
lean_dec(x_37);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_111, 2);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Language_Lean_isBeforeEditPos(x_113, x_3, x_110);
lean_dec(x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_box(0);
lean_inc(x_3);
x_119 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_118, x_3, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_dec(x_114);
x_121 = lean_ctor_get(x_16, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_16, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_123 = x_16;
} else {
 lean_dec_ref(x_16);
 x_123 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_121);
x_124 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_124, 0, x_121);
lean_closure_set(x_124, 1, x_3);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = 1;
x_127 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_122, x_124, x_125, x_126, x_120);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_14, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_132 = x_14;
} else {
 lean_dec_ref(x_14);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_123;
}
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_128);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = 0;
if (lean_is_scalar(x_132)) {
 x_137 = lean_alloc_ctor(0, 2, 1);
} else {
 x_137 = x_132;
}
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_136);
x_138 = lean_ctor_get(x_3, 3);
lean_inc(x_138);
lean_dec(x_3);
lean_ctor_set(x_29, 0, x_138);
lean_ctor_set(x_8, 4, x_29);
lean_ctor_set(x_8, 3, x_135);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_137);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_8);
lean_ctor_set(x_139, 1, x_129);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_123);
lean_dec(x_121);
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_140 = lean_ctor_get(x_127, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_127, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_142 = x_127;
} else {
 lean_dec_ref(x_127);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_free_object(x_29);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_37);
if (x_144 == 0)
{
return x_37;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_37, 0);
x_146 = lean_ctor_get(x_37, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_37);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_29, 0);
lean_inc(x_148);
lean_dec(x_29);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Lean_Language_SnapshotTask_get_x3f___rarg(x_149, x_33);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_box(0);
lean_inc(x_3);
x_154 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_153, x_3, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
lean_dec(x_150);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
lean_dec(x_155);
x_159 = lean_ctor_get(x_158, 2);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Lean_Language_Lean_isBeforeEditPos(x_160, x_3, x_157);
lean_dec(x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_156);
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_box(0);
lean_inc(x_3);
x_166 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_165, x_3, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
lean_dec(x_161);
x_168 = lean_ctor_get(x_16, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_16, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_170 = x_16;
} else {
 lean_dec_ref(x_16);
 x_170 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_168);
x_171 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_171, 0, x_168);
lean_closure_set(x_171, 1, x_3);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = 1;
x_174 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_169, x_171, x_172, x_173, x_167);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_14, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_179 = x_14;
} else {
 lean_dec_ref(x_14);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_170)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_170;
}
lean_ctor_set(x_181, 0, x_168);
lean_ctor_set(x_181, 1, x_175);
if (lean_is_scalar(x_156)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_156;
}
lean_ctor_set(x_182, 0, x_181);
x_183 = 0;
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 2, 1);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set_uint8(x_184, sizeof(void*)*2, x_183);
x_185 = lean_ctor_get(x_3, 3);
lean_inc(x_185);
lean_dec(x_3);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_8, 4, x_186);
lean_ctor_set(x_8, 3, x_182);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_184);
if (lean_is_scalar(x_177)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_177;
}
lean_ctor_set(x_187, 0, x_8);
lean_ctor_set(x_187, 1, x_176);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_156);
lean_free_object(x_8);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_188 = lean_ctor_get(x_174, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_174, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_190 = x_174;
} else {
 lean_dec_ref(x_174);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_150, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_150, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_194 = x_150;
} else {
 lean_dec_ref(x_150);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
}
}
else
{
uint8_t x_196; 
lean_free_object(x_8);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_24);
if (x_196 == 0)
{
return x_24;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_24, 0);
x_198 = lean_ctor_get(x_24, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_24);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; 
lean_dec(x_8);
x_200 = l_Lean_Language_SnapshotTask_get_x3f___rarg(x_17, x_4);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_box(0);
lean_inc(x_3);
x_204 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_203, x_3, x_202);
return x_204;
}
else
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
lean_dec(x_201);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
lean_dec(x_200);
x_207 = lean_box(0);
lean_inc(x_3);
x_208 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_207, x_3, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
lean_dec(x_200);
x_210 = lean_ctor_get(x_205, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_211 = x_205;
} else {
 lean_dec_ref(x_205);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Language_SnapshotTask_get_x3f___rarg(x_212, x_209);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_211);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_box(0);
lean_inc(x_3);
x_217 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_216, x_3, x_215);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_219 = x_214;
} else {
 lean_dec_ref(x_214);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_213, 1);
lean_inc(x_220);
lean_dec(x_213);
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_ctor_get(x_221, 2);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_Lean_Language_Lean_isBeforeEditPos(x_223, x_3, x_220);
lean_dec(x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_219);
lean_dec(x_211);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_box(0);
lean_inc(x_3);
x_229 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_13, x_1, x_3, x_2, x_228, x_3, x_227);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; 
lean_dec(x_2);
lean_dec(x_1);
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
lean_dec(x_224);
x_231 = lean_ctor_get(x_16, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_16, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_233 = x_16;
} else {
 lean_dec_ref(x_16);
 x_233 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_231);
x_234 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader___lambda__6), 4, 2);
lean_closure_set(x_234, 0, x_231);
lean_closure_set(x_234, 1, x_3);
x_235 = lean_ctor_get(x_232, 0);
lean_inc(x_235);
x_236 = 1;
x_237 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_232, x_234, x_235, x_236, x_230);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_14, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_242 = x_14;
} else {
 lean_dec_ref(x_14);
 x_242 = lean_box(0);
}
x_243 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_233;
}
lean_ctor_set(x_244, 0, x_231);
lean_ctor_set(x_244, 1, x_238);
if (lean_is_scalar(x_219)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_219;
}
lean_ctor_set(x_245, 0, x_244);
x_246 = 0;
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 2, 1);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_241);
lean_ctor_set(x_247, 1, x_243);
lean_ctor_set_uint8(x_247, sizeof(void*)*2, x_246);
x_248 = lean_ctor_get(x_3, 3);
lean_inc(x_248);
lean_dec(x_3);
if (lean_is_scalar(x_211)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_211;
}
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_13);
lean_ctor_set(x_250, 2, x_15);
lean_ctor_set(x_250, 3, x_245);
lean_ctor_set(x_250, 4, x_249);
if (lean_is_scalar(x_240)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_240;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_239);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_219);
lean_dec(x_211);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_252 = lean_ctor_get(x_237, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_237, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_254 = x_237;
} else {
 lean_dec_ref(x_237);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_211);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_ctor_get(x_213, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_213, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_258 = x_213;
} else {
 lean_dec_ref(x_213);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = lean_ctor_get(x_200, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_200, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_262 = x_200;
} else {
 lean_dec_ref(x_200);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_Lean_process_parseHeader___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Language_Lean_process_parseHeader___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_Lean_process_parseHeader___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Language_Lean_process_parseHeader___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process_parseHeader___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Language_Lean_process_parseHeader___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseHeader), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Language_Lean_LeanProcessingM_run___rarg(x_5, x_6, x_6, x_3, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_ctor_set(x_2, 0, x_10);
x_11 = lean_ctor_get(x_9, 4);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Language_Lean_LeanProcessingM_run___rarg(x_5, x_2, x_11, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Language_Lean_LeanProcessingM_run___rarg(x_5, x_15, x_16, x_3, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_processCommands(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd), 5, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = l_Lean_Language_Lean_LeanProcessingM_run___rarg(x_7, x_6, x_6, x_1, x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_ctor_set(x_4, 0, x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd), 5, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Language_Lean_LeanProcessingM_run___rarg(x_12, x_14, x_6, x_1, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Language_Lean_process_parseCmd), 5, 3);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Language_Lean_LeanProcessingM_run___rarg(x_19, x_21, x_6, x_1, x_5);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalEnv_x3f_goCmd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Language_SnapshotTask_get___rarg(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Language_SnapshotTask_get___rarg(x_9);
x_1 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_waitForFinalEnv_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Language_SnapshotTask_get___rarg(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Language_SnapshotTask_get___rarg(x_10);
x_12 = l_Lean_Language_Lean_waitForFinalEnv_x3f_goCmd(x_11);
return x_12;
}
}
}
}
lean_object* initialize_Lean_Language_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__1);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__2 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__2();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__2);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__3 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__3();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__3);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__4 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__4();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__4);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__5 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__5();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__5);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__6 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__6();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__6);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__7 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__7();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__7);
l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__8 = _init_l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__8();
lean_mark_persistent(l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37____closed__8);
if (builtin) {res = l_Lean_Language_Lean_initFn____x40_Lean_Language_Lean___hyg_37_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_Lean_stderrAsMessages = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_Lean_stderrAsMessages);
lean_dec_ref(res);
}l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandFinishedSnapshot___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__2 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__2);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___lambda__3___closed__3);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__1);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__2);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3 = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___closed__3);
l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot = _init_l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot);
l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1 = _init_l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_instToSnapshotTreeHeaderProcessedSnapshot___closed__1);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__1);
l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2 = _init_l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult___closed__2);
l_Lean_Language_Lean_SetupImportsResult_trustLevel___default = _init_l_Lean_Language_Lean_SetupImportsResult_trustLevel___default();
l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__1 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__1);
l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__2 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__2);
l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__3 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__3);
l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__4 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__4();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__4);
l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5 = _init_l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___at_Lean_Language_Lean_process_doElab___spec__1___closed__5);
l_Lean_Language_Lean_process_doElab___lambda__2___closed__1 = _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__2___closed__1);
l_Lean_Language_Lean_process_doElab___lambda__2___closed__2 = _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__2();
l_Lean_Language_Lean_process_doElab___lambda__2___closed__3 = _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__2___closed__3);
l_Lean_Language_Lean_process_doElab___lambda__2___closed__4 = _init_l_Lean_Language_Lean_process_doElab___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__2___closed__4);
l_Lean_Language_Lean_process_doElab___lambda__3___closed__1 = _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__3___closed__1);
l_Lean_Language_Lean_process_doElab___lambda__3___closed__2 = _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__3___closed__2);
l_Lean_Language_Lean_process_doElab___lambda__3___closed__3 = _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__3___closed__3);
l_Lean_Language_Lean_process_doElab___lambda__3___closed__4 = _init_l_Lean_Language_Lean_process_doElab___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Language_Lean_process_doElab___lambda__3___closed__4);
l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1 = _init_l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___lambda__3___closed__1);
l_Lean_Language_Lean_process_parseCmd___lambda__8___closed__1 = _init_l_Lean_Language_Lean_process_parseCmd___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___lambda__8___closed__1);
l_Lean_Language_Lean_process_parseCmd___closed__1 = _init_l_Lean_Language_Lean_process_parseCmd___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__1);
l_Lean_Language_Lean_process_parseCmd___closed__2 = _init_l_Lean_Language_Lean_process_parseCmd___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__2);
l_Lean_Language_Lean_process_parseCmd___closed__3 = _init_l_Lean_Language_Lean_process_parseCmd___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__3);
l_Lean_Language_Lean_process_parseCmd___closed__4 = _init_l_Lean_Language_Lean_process_parseCmd___closed__4();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__4);
l_Lean_Language_Lean_process_parseCmd___closed__5 = _init_l_Lean_Language_Lean_process_parseCmd___closed__5();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__5);
l_Lean_Language_Lean_process_parseCmd___closed__6 = _init_l_Lean_Language_Lean_process_parseCmd___closed__6();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__6);
l_Lean_Language_Lean_process_parseCmd___closed__7 = _init_l_Lean_Language_Lean_process_parseCmd___closed__7();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__7);
l_Lean_Language_Lean_process_parseCmd___closed__8 = _init_l_Lean_Language_Lean_process_parseCmd___closed__8();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__8);
l_Lean_Language_Lean_process_parseCmd___closed__9 = _init_l_Lean_Language_Lean_process_parseCmd___closed__9();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__9);
l_Lean_Language_Lean_process_parseCmd___closed__10 = _init_l_Lean_Language_Lean_process_parseCmd___closed__10();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__10);
l_Lean_Language_Lean_process_parseCmd___closed__11 = _init_l_Lean_Language_Lean_process_parseCmd___closed__11();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__11);
l_Lean_Language_Lean_process_parseCmd___closed__12 = _init_l_Lean_Language_Lean_process_parseCmd___closed__12();
lean_mark_persistent(l_Lean_Language_Lean_process_parseCmd___closed__12);
l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__1 = _init_l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__1();
lean_mark_persistent(l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__1);
l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2 = _init_l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2();
lean_mark_persistent(l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__2);
l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3 = _init_l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3();
lean_mark_persistent(l_List_map___at_Lean_Language_Lean_process_processHeader___spec__1___closed__3);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__1);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__2);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__3);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__4 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__4);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__5 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__5);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__6);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__7 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__7);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__8);
l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9 = _init_l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___lambda__3___closed__9);
l_Lean_Language_Lean_process_processHeader___closed__1 = _init_l_Lean_Language_Lean_process_processHeader___closed__1();
lean_mark_persistent(l_Lean_Language_Lean_process_processHeader___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

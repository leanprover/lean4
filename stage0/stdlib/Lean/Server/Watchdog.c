// Lean compiler output
// Module: Lean.Server.Watchdog
// Imports: Init Init.System.IO Init.Data.ByteArray Std.Data.RBMap Lean.Elab.Import Lean.Data.Lsp Lean.Server.FileSource Lean.Server.Utils
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
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10;
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_92_(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidOpen(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quote___closed__1;
lean_object* l_Lean_Server_Watchdog_handleRequest___closed__1;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__11___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonHoverParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_464_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonPlainGoalParams____x40_Lean_Data_Lsp_Extra___hyg_110_(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest___closed__2;
lean_object* l_Lean_Server_Watchdog_handleNotification___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2;
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_terminateFileWorker___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__3;
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__5;
extern lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
extern lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__6;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits___closed__3;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_eraseFileWorker___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdin___at_Lean_Server_Watchdog_watchdogMain___spec__1(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
lean_object* l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9;
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__6(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDeclarationParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_546_(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4(lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux(lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__9;
lean_object* l_Lean_Server_Watchdog_handleNotification___closed__2;
lean_object* l_IO_throwServerError___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__13(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__4;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__4;
extern lean_object* l_Lean_Lsp_SemanticTokenType_names;
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__8;
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_Server_Watchdog_parseParams(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__4;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__10;
lean_object* l_Lean_Server_Watchdog_workerCfg;
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3;
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__1;
lean_object* l_Lean_Server_Watchdog_terminateFileWorker(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42_(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
extern lean_object* l_Lean_Parser_Command_initialize___elambda__1___closed__1;
lean_object* l_Lean_Server_Watchdog_runClientTask___closed__1;
lean_object* l_Lean_Server_Watchdog_handleDidClose(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_exit___elambda__1___closed__1;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6;
extern lean_object* l_Task_Priority_dedicated;
extern lean_object* l_Lean_Lsp_msgToDiagnostic___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__3;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___closed__2;
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__2;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__7;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4;
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
lean_object* l_Lean_Server_Watchdog_mainLoop___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_FS_Stream_readLspNotificationAs___closed__1;
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_eraseFileWorker(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidClose___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_appendTrees___rarg(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_RBNode_isBlack___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonSemanticTokensRangeParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1515_(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_0__mkPanicMessage___closed__2;
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_63_(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDefinitionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_628_(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits_match__1(lean_object*);
extern lean_object* l_IO_FS_Stream_readRequestAs___closed__5;
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8;
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_watchdogMain___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCrash(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1;
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonSemanticTokensParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1455_(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2;
lean_object* l_Lean_Server_Watchdog_FileWorker_stdout(lean_object*);
lean_object* lean_server_watchdog_main(lean_object*, lean_object*);
uint8_t l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDocumentSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_935_(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_88_(lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1;
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6;
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9;
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_handleRequest___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__2;
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_302_(lean_object*);
extern lean_object* l_Task_Priority_default;
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8;
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidCloseTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_447_(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits___closed__2;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams_match__1(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__14___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_FS_Stream_readNotificationAs___closed__1;
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6;
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__6;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8;
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__1;
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1(lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__2___boxed(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__5;
lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__3;
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_281_(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
lean_object* l_Lean_Server_Watchdog_handleRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5;
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__5(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
lean_object* l_Lean_Server_Watchdog_watchdogMain___closed__1;
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__11;
lean_object* l_Lean_Server_Watchdog_FileWorker_stdin(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits___closed__1;
extern lean_object* l_IO_FS_Stream_readRequestAs___closed__2;
lean_object* l_Lean_Server_Watchdog_updateFileWorkers(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCrash___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__8;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1;
extern lean_object* l_IO_FS_Stream_readRequestAs___closed__1;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
extern lean_object* l_IO_FS_Stream_readLspRequestAs___closed__1;
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7;
lean_object* l_Lean_Server_Watchdog_handleEdits_match__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker___closed__1;
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__2(lean_object*);
lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_67_(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__2;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_updateFileWorkers___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonTypeDefinitionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_710_(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__4;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Server_Watchdog_findFileWorker___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__1;
lean_object* l_Lean_Server_Watchdog_handleEdits_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__2(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__13;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeSuffix;
lean_object* l_Lean_Server_Watchdog_handleCancelRequest(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_log(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_315_(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225_(lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6;
extern lean_object* l_Lean_getBuiltinSearchPath___closed__3;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__9;
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1;
uint8_t l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_457_(lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDocumentHighlightParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_792_(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed(lean_object*);
static lean_object* _init_l_Lean_Server_Watchdog_workerCfg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Elab_parseImports___closed__1;
x_4 = l_Lean_Parser_mkInputContext(x_1, x_3);
x_5 = l_Lean_Parser_parseHeader(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_stdin(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_stream_of_handle(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_stdout(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_stream_of_handle(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_readMessage_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(x_5);
x_9 = lean_apply_4(x_2, x_4, x_8, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_readMessage_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_1);
lean_inc(x_6);
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_6, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_8);
x_14 = 0;
lean_ctor_set(x_2, 3, x_13);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_2);
x_15 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_8);
x_16 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_5);
x_19 = 0;
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_5);
x_21 = l_Std_RBNode_balLeft___rarg(x_20, x_6, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_23);
lean_inc(x_1);
x_26 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc(x_1);
lean_inc(x_23);
x_27 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_28 = l_Std_RBNode_appendTrees___rarg(x_22, x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Std_RBNode_isBlack___rarg(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_25);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_25);
x_34 = l_Std_RBNode_balRight___rarg(x_22, x_23, x_24, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = l_Std_RBNode_isBlack___rarg(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_22);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_22);
x_40 = l_Std_RBNode_balLeft___rarg(x_39, x_23, x_24, x_25);
return x_40;
}
}
}
}
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
x_7 = lean_st_ref_take(x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(x_5, x_8);
x_11 = lean_st_ref_set(x_6, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = l_Lean_Server_Watchdog_FileWorker_stdout(x_1);
x_4 = l_IO_FS_Stream_readLspMessage(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_st_ref_take(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(x_7, x_10);
x_13 = lean_st_ref_set(x_8, x_12, x_11);
lean_dec(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(x_5, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(x_5, x_1, x_18, x_17);
lean_dec(x_1);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(x_1, x_2, x_3, x_9, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
lean_inc(x_3);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_2);
lean_inc(x_1);
x_21 = l_IO_FS_Stream_writeLspResponseError(x_1, x_20, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_4 = x_11;
x_5 = x_23;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_st_ref_take(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_st_ref_set(x_6, x_10, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(x_2, x_3, x_4, x_8, x_13, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Internal error: empty grouped edits reference in signal task");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_mono_ms_now(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 5);
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1;
x_11 = l_IO_throwServerError___rarg(x_10, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_nat_dec_le(x_16, x_4);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; lean_object* x_20; 
lean_free_object(x_7);
x_18 = lean_nat_sub(x_16, x_4);
lean_dec(x_4);
lean_dec(x_16);
x_19 = lean_uint32_of_nat(x_18);
lean_dec(x_18);
x_20 = l_IO_sleep(x_19, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_2 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_16);
lean_dec(x_4);
x_27 = lean_box(0);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_nat_dec_le(x_30, x_4);
if (x_31 == 0)
{
lean_object* x_32; uint32_t x_33; lean_object* x_34; 
x_32 = lean_nat_sub(x_30, x_4);
lean_dec(x_4);
lean_dec(x_30);
x_33 = lean_uint32_of_nat(x_32);
lean_dec(x_32);
x_34 = l_IO_sleep(x_33, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_2 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_30);
lean_dec(x_4);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
return x_3;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
return x_4;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Task_Priority_default;
x_5 = lean_io_as_task(x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_9 = lean_task_map(x_8, x_7, x_4);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_13 = lean_task_map(x_12, x_10, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_string_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_string_dec_lt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_string_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_string_dec_lt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_string_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_string_dec_lt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
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
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
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
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = lean_string_dec_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = lean_string_dec_lt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
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
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_updateFileWorkers(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(x_6, x_10, x_1);
x_12 = lean_st_ref_set(x_4, x_11, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Server_Watchdog_updateFileWorkers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_updateFileWorkers(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_findFileWorker_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_string_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findFileWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got unknown document URI (");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
x_10 = l_Lean_Server_Watchdog_findFileWorker___closed__1;
x_11 = lean_string_append(x_10, x_1);
x_12 = l_prec_x28___x29___closed__7;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_8);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(x_16, x_1);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lean_Server_Watchdog_findFileWorker___closed__1;
x_20 = lean_string_append(x_19, x_1);
x_21 = l_prec_x28___x29___closed__7;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_IO_throwServerError___rarg(x_22, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
}
}
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_string_dec_lt(x_1, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_string_dec_lt(x_6, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_8);
x_14 = 0;
lean_ctor_set(x_2, 3, x_13);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_2);
x_15 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_8);
x_16 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_5);
x_19 = 0;
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_5);
x_21 = l_Std_RBNode_balLeft___rarg(x_20, x_6, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = lean_string_dec_lt(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_string_dec_lt(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
x_28 = l_Std_RBNode_appendTrees___rarg(x_22, x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Std_RBNode_isBlack___rarg(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_25);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_25);
x_34 = l_Std_RBNode_balRight___rarg(x_22, x_23, x_24, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = l_Std_RBNode_isBlack___rarg(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_22);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_22);
x_40 = l_Std_RBNode_balLeft___rarg(x_39, x_23, x_24, x_25);
return x_40;
}
}
}
}
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_eraseFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(x_1, x_6);
x_9 = lean_st_ref_set(x_4, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_eraseFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 10;
x_7 = lean_string_push(x_2, x_6);
x_8 = lean_apply_2(x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_log(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(x_4, x_1, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
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
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(x_1, x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Server process for ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" crashed, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("likely due to a stack overflow in user code");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("see stderr for exception");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("The file worker has been terminated. Either the header has changed,");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" or the file was closed, or the server is shutting down.");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
x_2 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_73; 
lean_inc(x_1);
x_73 = l_Lean_Server_Watchdog_FileWorker_readMessage(x_1, x_4);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_2);
x_76 = l_IO_FS_Stream_writeLspMessage(x_2, x_74, x_75);
lean_dec(x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_5 = x_80;
x_6 = x_78;
goto block_10;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_11 = x_81;
x_12 = x_82;
goto block_72;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_dec(x_73);
x_11 = x_83;
x_12 = x_84;
goto block_72;
}
block_10:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
block_72:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = l_Lean_Server_Watchdog_workerCfg;
x_15 = lean_io_process_child_wait(x_14, x_13, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = lean_unbox_uint32(x_16);
x_20 = x_19 == x_18;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; uint32_t x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = 1;
x_29 = lean_unbox_uint32(x_16);
lean_dec(x_16);
x_30 = x_29 == x_28;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_31 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
x_32 = lean_string_append(x_27, x_31);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = 4;
lean_inc(x_2);
x_36 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_35, x_34, x_17);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_11);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_5 = x_40;
x_6 = x_37;
goto block_10;
}
else
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
x_46 = lean_string_append(x_27, x_45);
x_47 = l_Lean_Name_toString___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = 4;
lean_inc(x_2);
x_50 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_49, x_48, x_17);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_11);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_5 = x_54;
x_6 = x_51;
goto block_10;
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_16);
lean_dec(x_11);
x_59 = 10;
x_60 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7;
lean_inc(x_2);
x_61 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_59, x_60, x_17);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8;
x_5 = x_63;
x_6 = x_62;
goto block_10;
}
else
{
uint8_t x_64; 
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
}
else
{
uint8_t x_68; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_15);
if (x_68 == 0)
{
return x_15;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_15, 0);
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_15);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Task_Priority_dedicated;
x_7 = lean_io_as_task(x_5, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_11 = l_Task_Priority_default;
x_12 = lean_task_map(x_10, x_9, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_16 = l_Task_Priority_default;
x_17 = lean_task_map(x_15, x_13, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_mk_ref(x_1, x_3);
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
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_mk_ref(x_1, x_3);
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
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_67_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__6(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("--worker");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didOpen");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_startFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_7);
x_8 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 7);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
x_13 = l_List_redLength___rarg(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = l_List_toArrayAux___rarg(x_12, x_14);
x_16 = l_Lean_Server_Watchdog_startFileWorker___closed__2;
x_17 = l_Array_append___rarg(x_16, x_15);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_Server_Watchdog_workerCfg;
x_20 = l_Array_empty___closed__1;
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_11);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_io_process_spawn(x_21, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__1(x_25, x_2, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(x_18, x_2, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_9);
x_33 = l_Lean_Server_Watchdog_startFileWorker___closed__3;
x_34 = lean_box(1);
lean_inc(x_30);
lean_inc(x_27);
lean_inc(x_23);
lean_inc(x_32);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_30);
lean_inc(x_2);
x_36 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(x_35, x_2, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_27);
lean_ctor_set(x_39, 5, x_30);
lean_inc(x_39);
x_40 = l_Lean_Server_Watchdog_FileWorker_stdin(x_39);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_41);
x_42 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_43 = l_Lean_Parser_Command_initialize___elambda__1___closed__1;
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
lean_inc(x_40);
x_45 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__3(x_40, x_44, x_38);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_getBuiltinSearchPath___closed__3;
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_5);
lean_ctor_set(x_48, 3, x_7);
x_49 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__5(x_40, x_50, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Server_Watchdog_updateFileWorkers(x_39, x_2, x_52);
lean_dec(x_2);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_39);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_36);
if (x_62 == 0)
{
return x_36;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_36, 0);
x_64 = lean_ctor_get(x_36, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_36);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_22);
if (x_66 == 0)
{
return x_22;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_22, 0);
x_68 = lean_ctor_get(x_22, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_22);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_8);
if (x_70 == 0)
{
return x_8;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_8, 0);
x_72 = lean_ctor_get(x_8, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_8);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_terminateFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Server_Watchdog_FileWorker_stdin(x_5);
x_8 = l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
x_9 = l_IO_FS_Stream_writeLspMessage(x_7, x_8, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Server_Watchdog_terminateFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_terminateFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleCrash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_6, 3, x_10);
x_11 = l_Lean_Server_Watchdog_updateFileWorkers(x_6, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_ctor_get(x_6, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_16);
x_19 = l_Lean_Server_Watchdog_updateFileWorkers(x_18, x_3, x_7);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_handleCrash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleCrash(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_tryWriteMessage_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_tryWriteMessage_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
x_12 = l_IO_FS_Stream_writeLspMessage(x_11, x_10, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 1;
x_15 = x_4 + x_14;
x_4 = x_15;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_array_push(x_5, x_10);
x_19 = 1;
x_20 = x_4 + x_19;
x_4 = x_20;
x_5 = x_18;
x_7 = x_17;
goto _start;
}
}
}
}
static uint8_t _init_l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
if (x_4 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(x_2, x_3, x_1, x_10, x_11, x_7, x_8);
lean_dec(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_array_push(x_13, x_5);
x_15 = lean_box(0);
x_16 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(x_2, x_3, x_1, x_14, x_15, x_7, x_8);
lean_dec(x_14);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
if (x_4 == 0)
{
lean_object* x_18; 
x_18 = l_IO_FS_Stream_writeLspMessage(x_17, x_5, x_8);
lean_dec(x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Array_empty___closed__1;
x_21 = l_Lean_Server_Watchdog_handleCrash(x_3, x_20, x_7, x_19);
lean_dec(x_7);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_5);
x_23 = lean_array_push(x_22, x_5);
x_24 = l_IO_FS_Stream_writeLspMessage(x_17, x_5, x_8);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Server_Watchdog_handleCrash(x_3, x_23, x_7, x_25);
lean_dec(x_7);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_18 = lean_ctor_get(x_8, 5);
lean_inc(x_18);
x_19 = lean_st_ref_take(x_18, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_st_ref_set(x_18, x_22, x_21);
lean_dec(x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 0;
x_11 = x_25;
x_12 = x_24;
goto block_17;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_2);
x_31 = lean_array_push(x_30, x_2);
lean_ctor_set(x_27, 3, x_31);
x_32 = lean_st_ref_set(x_18, x_20, x_28);
lean_dec(x_18);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
x_11 = x_34;
x_12 = x_33;
goto block_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_37 = lean_ctor_get(x_27, 2);
x_38 = lean_ctor_get(x_27, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
lean_inc(x_2);
x_39 = lean_array_push(x_38, x_2);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_20, 0, x_40);
x_41 = lean_st_ref_set(x_18, x_20, x_28);
lean_dec(x_18);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = 1;
x_11 = x_43;
x_12 = x_42;
goto block_17;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 3);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
lean_inc(x_2);
x_51 = lean_array_push(x_49, x_2);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_st_ref_set(x_18, x_53, x_45);
lean_dec(x_18);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = 1;
x_11 = x_56;
x_12 = x_55;
goto block_17;
}
}
block_17:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(x_8, x_4, x_1, x_3, x_2, x_13, x_5, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_5);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_7);
if (x_57 == 0)
{
return x_7;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_7, 0);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_7);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(x_1, x_9, x_3, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_FileMap_ofString(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Lean_Server_Watchdog_startFileWorker(x_8, x_2, x_3);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleEdits_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleEdits_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_281_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_4);
x_11 = 1;
x_12 = 0;
lean_inc(x_6);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage(x_1, x_10, x_11, x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = x_4 + x_15;
x_17 = lean_box(0);
x_4 = x_16;
x_5 = x_17;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didChange");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Server_foldDocumentChanges(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_20);
lean_inc(x_3);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_22, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Syntax_structEq(x_24, x_17);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_1);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = l_Lean_Server_Watchdog_terminateFileWorker(x_3, x_13, x_25);
lean_dec(x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Server_Watchdog_startFileWorker(x_21, x_13, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_ctor_set(x_1, 0, x_21);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_6);
lean_ctor_set(x_30, 3, x_7);
lean_ctor_set(x_30, 4, x_8);
lean_ctor_set(x_30, 5, x_9);
x_31 = l_Lean_Server_Watchdog_updateFileWorkers(x_30, x_13, x_25);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(x_10);
x_34 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = 1;
lean_inc(x_13);
x_37 = l_Lean_Server_Watchdog_tryWriteMessage(x_3, x_35, x_36, x_36, x_13, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_11, 3);
x_40 = lean_array_get_size(x_39);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = 0;
x_43 = lean_box(0);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(x_3, x_39, x_41, x_42, x_43, x_13, x_38);
lean_dec(x_3);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_21);
lean_free_object(x_1);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_23);
if (x_57 == 0)
{
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_1);
x_63 = lean_ctor_get(x_61, 2);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Server_foldDocumentChanges(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_65);
lean_inc(x_3);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_4);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_67, x_14);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Syntax_structEq(x_69, x_62);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = l_Lean_Server_Watchdog_terminateFileWorker(x_3, x_13, x_70);
lean_dec(x_3);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Server_Watchdog_startFileWorker(x_66, x_13, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_62);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_5);
lean_ctor_set(x_76, 2, x_6);
lean_ctor_set(x_76, 3, x_7);
lean_ctor_set(x_76, 4, x_8);
lean_ctor_set(x_76, 5, x_9);
x_77 = l_Lean_Server_Watchdog_updateFileWorkers(x_76, x_13, x_70);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(x_10);
x_80 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = 1;
lean_inc(x_13);
x_83 = l_Lean_Server_Watchdog_tryWriteMessage(x_3, x_81, x_82, x_82, x_13, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_11, 3);
x_86 = lean_array_get_size(x_85);
x_87 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_88 = 0;
x_89 = lean_box(0);
x_90 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(x_3, x_85, x_87, x_88, x_89, x_13, x_84);
lean_dec(x_3);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_13);
lean_dec(x_3);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_100 = x_83;
} else {
 lean_dec_ref(x_83);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_66);
lean_dec(x_62);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_102 = lean_ctor_get(x_68, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_68, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_104 = x_68;
} else {
 lean_dec_ref(x_68);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Array_isEmpty___rarg(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Server_Watchdog_handleEdits___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Internal error: empty grouped edits reference");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected version number");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got outdated version number");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_st_ref_take(x_9, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_st_ref_set(x_9, x_13, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Server_Watchdog_handleEdits___closed__1;
x_17 = l_IO_throwServerError___rarg(x_16, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Server_Watchdog_handleEdits___closed__2;
x_24 = l_IO_throwServerError___rarg(x_23, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_nat_dec_le(x_27, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l_Lean_Server_Watchdog_handleEdits___lambda__2(x_4, x_28, x_26, x_27, x_5, x_6, x_7, x_8, x_9, x_19, x_18, x_32, x_2, x_25);
lean_dec(x_18);
lean_dec(x_28);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_34 = l_Lean_Server_Watchdog_handleEdits___closed__3;
x_35 = l_IO_throwServerError___rarg(x_34, x_25);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Server_Watchdog_handleEdits___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Server_Watchdog_handleEdits___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidClose(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_terminateFileWorker(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidClose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_handleDidClose(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleCancelRequest_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleCancelRequest_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_inc(x_2);
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_63_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/cancelRequest");
return x_1;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(x_1, x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_10, 4);
x_20 = lean_st_ref_take(x_19, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
lean_inc(x_21);
x_23 = l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(x_21, x_1);
lean_inc(x_1);
x_24 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(x_1, x_21);
x_25 = lean_st_ref_set(x_19, x_24, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_2 = x_11;
x_3 = x_27;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_23);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(x_1);
x_31 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = 0;
lean_inc(x_4);
x_34 = l_Lean_Server_Watchdog_tryWriteMessage(x_9, x_32, x_33, x_33, x_4, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_2 = x_11;
x_3 = x_36;
x_5 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
x_5 = lean_st_ref_get(x_4, x_3);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(x_1, x_6, x_8, x_2, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_parseParams_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got param with wrong structure: ");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Json_compress(x_2);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_IO_throwServerError___rarg(x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_parseParams___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_parseParams___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleRequest_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/completion");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/hover");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/definition");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/typeDefinition");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/documentHighlight");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/documentSymbol");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/semanticTokens/range");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/semanticTokens/full");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/lean/plainGoal");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
x_15 = lean_string_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_16 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1;
x_17 = lean_string_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
x_18 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2;
x_19 = lean_string_dec_eq(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
x_20 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3;
x_21 = lean_string_dec_eq(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
x_22 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4;
x_23 = lean_string_dec_eq(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_6);
x_24 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5;
x_25 = lean_string_dec_eq(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_7);
x_26 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6;
x_27 = lean_string_dec_eq(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_8);
x_28 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7;
x_29 = lean_string_dec_eq(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_9);
x_30 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8;
x_31 = lean_string_dec_eq(x_1, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_10);
x_32 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9;
x_33 = lean_string_dec_eq(x_1, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_11);
x_34 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10;
x_35 = lean_string_dec_eq(x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_12);
x_36 = lean_apply_1(x_13, x_1);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = lean_apply_1(x_12, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_apply_1(x_11, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_apply_1(x_10, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_apply_1(x_9, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_apply_1(x_8, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_apply_1(x_7, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_apply_1(x_6, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_apply_1(x_5, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_apply_1(x_4, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_apply_1(x_3, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_apply_1(x_2, x_57);
return x_58;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleRequest_match__2___rarg), 13, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonPlainGoalParams____x40_Lean_Data_Lsp_Extra___hyg_110_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__2(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_10);
x_14 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_21);
lean_inc(x_2);
x_24 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_2);
lean_inc(x_21);
x_25 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_inc(x_2);
x_39 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
lean_inc(x_2);
lean_inc(x_36);
x_40 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
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
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
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
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
lean_inc(x_366);
lean_inc(x_2);
x_369 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
lean_inc(x_2);
lean_inc(x_366);
x_370 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
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
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_handleRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_handleRequest___spec__4(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonSemanticTokensParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1455_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonSemanticTokensRangeParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_1515_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDocumentSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_935_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDocumentHighlightParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_792_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonTypeDefinitionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_710_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDefinitionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_628_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDeclarationParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_546_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonHoverParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_464_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonCompletionParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_302_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_5, 4);
x_9 = lean_st_ref_take(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__2(x_1);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_12);
lean_inc(x_13);
x_14 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_handleRequest___spec__3(x_10, x_2, x_13);
x_15 = lean_st_ref_set(x_8, x_14, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = 0;
x_19 = l_Lean_Server_Watchdog_tryWriteMessage(x_4, x_13, x_17, x_18, x_6, x_16);
return x_19;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unsupported request method: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot process request to closed file '");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
x_7 = lean_string_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1;
x_9 = lean_string_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2;
x_11 = lean_string_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3;
x_13 = lean_string_dec_eq(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4;
x_15 = lean_string_dec_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5;
x_17 = lean_string_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6;
x_19 = lean_string_dec_eq(x_2, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7;
x_21 = lean_string_dec_eq(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8;
x_23 = lean_string_dec_eq(x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9;
x_25 = lean_string_dec_eq(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10;
x_27 = lean_string_dec_eq(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = l_Lean_Server_Watchdog_handleRequest___closed__1;
x_30 = lean_string_append(x_29, x_2);
lean_dec(x_2);
x_31 = l_Lean_instInhabitedParserDescr___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_box(0);
x_34 = 2;
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_34);
x_36 = l_IO_FS_Stream_writeLspResponseError(x_28, x_35, x_5);
lean_dec(x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_inc(x_3);
x_37 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(x_3, x_4, x_5);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Server_Watchdog_findFileWorker(x_40, x_4, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_40, x_42, x_4, x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_dec(x_4);
x_47 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_48 = lean_string_append(x_47, x_40);
lean_dec(x_40);
x_49 = l_Char_quote___closed__1;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_box(0);
x_52 = 10;
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_52);
x_54 = l_IO_FS_Stream_writeLspResponseError(x_46, x_53, x_45);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
return x_37;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_37);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
lean_inc(x_3);
x_69 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__5(x_3, x_4, x_5);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Server_Watchdog_findFileWorker(x_70, x_4, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_70, x_73, x_4, x_74);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_3);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
lean_dec(x_4);
x_78 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_79 = lean_string_append(x_78, x_70);
lean_dec(x_70);
x_80 = l_Char_quote___closed__1;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_box(0);
x_83 = 10;
x_84 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_83);
x_85 = l_IO_FS_Stream_writeLspResponseError(x_77, x_84, x_76);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_85);
if (x_92 == 0)
{
return x_85;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_85, 0);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_85);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_69);
if (x_96 == 0)
{
return x_69;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_69, 0);
x_98 = lean_ctor_get(x_69, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_69);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; 
lean_inc(x_3);
x_100 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__6(x_3, x_4, x_5);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Server_Watchdog_findFileWorker(x_103, x_4, x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_103, x_105, x_4, x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_3);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec(x_104);
x_109 = lean_ctor_get(x_4, 1);
lean_inc(x_109);
lean_dec(x_4);
x_110 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_111 = lean_string_append(x_110, x_103);
lean_dec(x_103);
x_112 = l_Char_quote___closed__1;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_box(0);
x_115 = 10;
x_116 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*3, x_115);
x_117 = l_IO_FS_Stream_writeLspResponseError(x_109, x_116, x_108);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
return x_117;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_117, 0);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_117);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_100);
if (x_128 == 0)
{
return x_100;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_100, 0);
x_130 = lean_ctor_get(x_100, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_100);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; 
lean_inc(x_3);
x_132 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(x_3, x_4, x_5);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Server_Watchdog_findFileWorker(x_133, x_4, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_133, x_136, x_4, x_137);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_3);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_ctor_get(x_4, 1);
lean_inc(x_140);
lean_dec(x_4);
x_141 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_142 = lean_string_append(x_141, x_133);
lean_dec(x_133);
x_143 = l_Char_quote___closed__1;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_box(0);
x_146 = 10;
x_147 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_144);
lean_ctor_set(x_147, 2, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*3, x_146);
x_148 = l_IO_FS_Stream_writeLspResponseError(x_140, x_147, x_139);
lean_dec(x_147);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
lean_dec(x_150);
x_151 = lean_box(0);
lean_ctor_set(x_148, 0, x_151);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_148);
if (x_155 == 0)
{
return x_148;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_148, 0);
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_148);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_132);
if (x_159 == 0)
{
return x_132;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_132, 0);
x_161 = lean_ctor_get(x_132, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_132);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_163; 
lean_inc(x_3);
x_163 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(x_3, x_4, x_5);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Server_Watchdog_findFileWorker(x_166, x_4, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_166, x_168, x_4, x_169);
lean_dec(x_168);
lean_dec(x_166);
lean_dec(x_3);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
lean_dec(x_167);
x_172 = lean_ctor_get(x_4, 1);
lean_inc(x_172);
lean_dec(x_4);
x_173 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_174 = lean_string_append(x_173, x_166);
lean_dec(x_166);
x_175 = l_Char_quote___closed__1;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_box(0);
x_178 = 10;
x_179 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*3, x_178);
x_180 = l_IO_FS_Stream_writeLspResponseError(x_172, x_179, x_171);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_180, 0);
lean_dec(x_182);
x_183 = lean_box(0);
lean_ctor_set(x_180, 0, x_183);
return x_180;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_180);
if (x_187 == 0)
{
return x_180;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_180, 0);
x_189 = lean_ctor_get(x_180, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_180);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_163);
if (x_191 == 0)
{
return x_163;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_163, 0);
x_193 = lean_ctor_get(x_163, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_163);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
else
{
lean_object* x_195; 
lean_inc(x_3);
x_195 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__9(x_3, x_4, x_5);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Server_Watchdog_findFileWorker(x_198, x_4, x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_198, x_200, x_4, x_201);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_3);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_3);
lean_dec(x_2);
x_203 = lean_ctor_get(x_199, 1);
lean_inc(x_203);
lean_dec(x_199);
x_204 = lean_ctor_get(x_4, 1);
lean_inc(x_204);
lean_dec(x_4);
x_205 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_206 = lean_string_append(x_205, x_198);
lean_dec(x_198);
x_207 = l_Char_quote___closed__1;
x_208 = lean_string_append(x_206, x_207);
x_209 = lean_box(0);
x_210 = 10;
x_211 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_211, 0, x_1);
lean_ctor_set(x_211, 1, x_208);
lean_ctor_set(x_211, 2, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*3, x_210);
x_212 = l_IO_FS_Stream_writeLspResponseError(x_204, x_211, x_203);
lean_dec(x_211);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
x_215 = lean_box(0);
lean_ctor_set(x_212, 0, x_215);
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_212);
if (x_219 == 0)
{
return x_212;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_212, 0);
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_212);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = !lean_is_exclusive(x_195);
if (x_223 == 0)
{
return x_195;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_195, 0);
x_225 = lean_ctor_get(x_195, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_195);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
else
{
lean_object* x_227; 
lean_inc(x_3);
x_227 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__10(x_3, x_4, x_5);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l_Lean_Server_Watchdog_findFileWorker(x_230, x_4, x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_230, x_232, x_4, x_233);
lean_dec(x_232);
lean_dec(x_230);
lean_dec(x_3);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_3);
lean_dec(x_2);
x_235 = lean_ctor_get(x_231, 1);
lean_inc(x_235);
lean_dec(x_231);
x_236 = lean_ctor_get(x_4, 1);
lean_inc(x_236);
lean_dec(x_4);
x_237 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_238 = lean_string_append(x_237, x_230);
lean_dec(x_230);
x_239 = l_Char_quote___closed__1;
x_240 = lean_string_append(x_238, x_239);
x_241 = lean_box(0);
x_242 = 10;
x_243 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_243, 1, x_240);
lean_ctor_set(x_243, 2, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*3, x_242);
x_244 = l_IO_FS_Stream_writeLspResponseError(x_236, x_243, x_235);
lean_dec(x_243);
if (lean_obj_tag(x_244) == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_244, 0);
lean_dec(x_246);
x_247 = lean_box(0);
lean_ctor_set(x_244, 0, x_247);
return x_244;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
lean_dec(x_244);
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_244);
if (x_251 == 0)
{
return x_244;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_244, 0);
x_253 = lean_ctor_get(x_244, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_244);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_227);
if (x_255 == 0)
{
return x_227;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_227, 0);
x_257 = lean_ctor_get(x_227, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_227);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
else
{
lean_object* x_259; 
lean_inc(x_3);
x_259 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__11(x_3, x_4, x_5);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
lean_dec(x_260);
x_263 = l_Lean_Server_Watchdog_findFileWorker(x_262, x_4, x_261);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_262, x_264, x_4, x_265);
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_3);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_3);
lean_dec(x_2);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
lean_dec(x_263);
x_268 = lean_ctor_get(x_4, 1);
lean_inc(x_268);
lean_dec(x_4);
x_269 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_270 = lean_string_append(x_269, x_262);
lean_dec(x_262);
x_271 = l_Char_quote___closed__1;
x_272 = lean_string_append(x_270, x_271);
x_273 = lean_box(0);
x_274 = 10;
x_275 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_275, 0, x_1);
lean_ctor_set(x_275, 1, x_272);
lean_ctor_set(x_275, 2, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*3, x_274);
x_276 = l_IO_FS_Stream_writeLspResponseError(x_268, x_275, x_267);
lean_dec(x_275);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 0);
lean_dec(x_278);
x_279 = lean_box(0);
lean_ctor_set(x_276, 0, x_279);
return x_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec(x_276);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_276);
if (x_283 == 0)
{
return x_276;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_276, 0);
x_285 = lean_ctor_get(x_276, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_276);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_287 = !lean_is_exclusive(x_259);
if (x_287 == 0)
{
return x_259;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_259, 0);
x_289 = lean_ctor_get(x_259, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_259);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
}
else
{
lean_object* x_291; 
lean_inc(x_3);
x_291 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__12(x_3, x_4, x_5);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_ctor_get(x_292, 0);
lean_inc(x_294);
lean_dec(x_292);
x_295 = l_Lean_Server_Watchdog_findFileWorker(x_294, x_4, x_293);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_294, x_296, x_4, x_297);
lean_dec(x_296);
lean_dec(x_294);
lean_dec(x_3);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_3);
lean_dec(x_2);
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
lean_dec(x_295);
x_300 = lean_ctor_get(x_4, 1);
lean_inc(x_300);
lean_dec(x_4);
x_301 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_302 = lean_string_append(x_301, x_294);
lean_dec(x_294);
x_303 = l_Char_quote___closed__1;
x_304 = lean_string_append(x_302, x_303);
x_305 = lean_box(0);
x_306 = 10;
x_307 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_307, 0, x_1);
lean_ctor_set(x_307, 1, x_304);
lean_ctor_set(x_307, 2, x_305);
lean_ctor_set_uint8(x_307, sizeof(void*)*3, x_306);
x_308 = l_IO_FS_Stream_writeLspResponseError(x_300, x_307, x_299);
lean_dec(x_307);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
lean_dec(x_310);
x_311 = lean_box(0);
lean_ctor_set(x_308, 0, x_311);
return x_308;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_box(0);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_308);
if (x_315 == 0)
{
return x_308;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_308, 0);
x_317 = lean_ctor_get(x_308, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_308);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_291);
if (x_319 == 0)
{
return x_291;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_291, 0);
x_321 = lean_ctor_get(x_291, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_291);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
}
else
{
lean_object* x_323; 
lean_inc(x_3);
x_323 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__13(x_3, x_4, x_5);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
lean_dec(x_324);
x_327 = l_Lean_Server_Watchdog_findFileWorker(x_326, x_4, x_325);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_326, x_328, x_4, x_329);
lean_dec(x_328);
lean_dec(x_326);
lean_dec(x_3);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_3);
lean_dec(x_2);
x_331 = lean_ctor_get(x_327, 1);
lean_inc(x_331);
lean_dec(x_327);
x_332 = lean_ctor_get(x_4, 1);
lean_inc(x_332);
lean_dec(x_4);
x_333 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_334 = lean_string_append(x_333, x_326);
lean_dec(x_326);
x_335 = l_Char_quote___closed__1;
x_336 = lean_string_append(x_334, x_335);
x_337 = lean_box(0);
x_338 = 10;
x_339 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_339, 0, x_1);
lean_ctor_set(x_339, 1, x_336);
lean_ctor_set(x_339, 2, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*3, x_338);
x_340 = l_IO_FS_Stream_writeLspResponseError(x_332, x_339, x_331);
lean_dec(x_339);
if (lean_obj_tag(x_340) == 0)
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_340, 0);
lean_dec(x_342);
x_343 = lean_box(0);
lean_ctor_set(x_340, 0, x_343);
return x_340;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
lean_dec(x_340);
x_345 = lean_box(0);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
else
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_340);
if (x_347 == 0)
{
return x_340;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_340, 0);
x_349 = lean_ctor_get(x_340, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_340);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_323);
if (x_351 == 0)
{
return x_323;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_323, 0);
x_353 = lean_ctor_get(x_323, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_323);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
}
else
{
lean_object* x_355; 
lean_inc(x_3);
x_355 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__14(x_3, x_4, x_5);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_ctor_get(x_356, 0);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Server_Watchdog_findFileWorker(x_358, x_4, x_357);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_3, x_1, x_2, x_358, x_360, x_4, x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_3);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_3);
lean_dec(x_2);
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
lean_dec(x_359);
x_364 = lean_ctor_get(x_4, 1);
lean_inc(x_364);
lean_dec(x_4);
x_365 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_366 = lean_string_append(x_365, x_358);
lean_dec(x_358);
x_367 = l_Char_quote___closed__1;
x_368 = lean_string_append(x_366, x_367);
x_369 = lean_box(0);
x_370 = 10;
x_371 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_371, 0, x_1);
lean_ctor_set(x_371, 1, x_368);
lean_ctor_set(x_371, 2, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*3, x_370);
x_372 = l_IO_FS_Stream_writeLspResponseError(x_364, x_371, x_363);
lean_dec(x_371);
if (lean_obj_tag(x_372) == 0)
{
uint8_t x_373; 
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_372, 0);
lean_dec(x_374);
x_375 = lean_box(0);
lean_ctor_set(x_372, 0, x_375);
return x_372;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
lean_dec(x_372);
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
else
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_372);
if (x_379 == 0)
{
return x_372;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_372, 0);
x_381 = lean_ctor_get(x_372, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_372);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
else
{
uint8_t x_383; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_383 = !lean_is_exclusive(x_355);
if (x_383 == 0)
{
return x_355;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_355, 0);
x_385 = lean_ctor_get(x_355, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_355);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__10(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__11(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__12(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__13(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__14(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didClose");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_8 = l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_apply_1(x_5, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_3, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleNotification_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 10;
x_7 = lean_string_push(x_2, x_6);
x_8 = lean_apply_2(x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_88_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidCloseTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_447_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_92_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got unsupported notification: ");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1;
x_8 = lean_string_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
x_11 = l_Lean_Server_Watchdog_handleNotification___closed__1;
x_12 = l_String_isPrefixOf(x_11, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = l_Lean_Server_Watchdog_handleNotification___closed__2;
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Lean_instInhabitedParserDescr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(x_13, x_17, x_3, x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(x_2, x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Server_Watchdog_handleCancelRequest(x_22, x_3, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(x_2, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Server_Watchdog_terminateFileWorker(x_30, x_3, x_31);
lean_dec(x_3);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(x_2, x_3, x_4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Server_Watchdog_handleDidOpen(x_38, x_3, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleNotification(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_io_wait(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_1 = x_9;
x_2 = x_20;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_7, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Server_Watchdog_terminateFileWorker(x_8, x_3, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_1 = x_9;
x_2 = x_14;
x_4 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_shutdown(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_5, x_19, x_1, x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_7 = x_21;
goto block_18;
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_5, x_8, x_1, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_shutdown(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_runClientTask_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
return x_4;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_runClientTask___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_runClientTask___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_runClientTask___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_readLspMessage), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Server_Watchdog_runClientTask___closed__1;
x_6 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Task_Priority_default;
x_8 = lean_io_as_task(x_6, x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Server_Watchdog_runClientTask___closed__2;
x_12 = lean_task_map(x_11, x_10, x_7);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lean_Server_Watchdog_runClientTask___closed__2;
x_16 = lean_task_map(x_15, x_13, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Watchdog_runClientTask___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("shutdown");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1;
x_11 = lean_string_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_12 = lean_apply_1(x_6, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_apply_3(x_3, x_7, x_8, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_apply_2(x_2, x_7, x_9);
return x_15;
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_19 = lean_string_dec_eq(x_16, x_18);
if (x_19 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_5);
x_20 = lean_apply_1(x_6, x_1);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_apply_2(x_5, x_16, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_26; 
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_18);
x_26 = lean_apply_1(x_6, x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_1);
lean_dec(x_6);
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_apply_1(x_4, x_27);
return x_28;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_17);
x_30 = lean_apply_1(x_6, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_apply_1(x_4, x_31);
return x_32;
}
}
}
}
default: 
{
lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_apply_1(x_6, x_1);
return x_33;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__2___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_5, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_3, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__3___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__4___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_315_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3(x_7, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_1 = x_9;
x_2 = x_14;
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_8);
x_18 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3___lambda__1), 2, 1);
lean_closure_set(x_18, 0, x_8);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = l_Task_Priority_default;
lean_inc(x_18);
x_21 = lean_task_map(x_18, x_19, x_20);
x_22 = lean_array_push(x_17, x_21);
x_23 = lean_ctor_get(x_8, 5);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_st_ref_get(x_23, x_16);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_1 = x_9;
x_2 = x_22;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_task_map(x_18, x_30, x_20);
x_32 = lean_array_push(x_22, x_31);
x_1 = x_9;
x_2 = x_32;
x_4 = x_28;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Server_Watchdog_runClientTask(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Server_Watchdog_mainLoop(x_5, x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Internal server error: got termination event for worker that should have been removed");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO error while processing events for ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got invalid JSON-RPC message");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("File changed.");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_658 = lean_ctor_get(x_2, 4);
lean_inc(x_658);
x_659 = lean_st_ref_get(x_658, x_3);
lean_dec(x_658);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
lean_dec(x_659);
x_662 = l_Array_empty___closed__1;
x_663 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3(x_660, x_662, x_2, x_661);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = lean_ctor_get(x_664, 0);
lean_inc(x_666);
lean_dec(x_664);
x_4 = x_666;
x_5 = x_665;
goto block_657;
block_657:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = lean_array_push(x_4, x_1);
x_7 = lean_array_to_list(lean_box(0), x_6);
x_8 = lean_io_wait_any(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_2);
x_13 = l_Lean_Server_Watchdog_handleEdits(x_12, x_2, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lean_Server_Watchdog_mainLoop___closed__1;
x_22 = l_IO_throwServerError___rarg(x_21, x_20);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Array_empty___closed__1;
x_29 = l_Lean_Server_Watchdog_handleCrash(x_27, x_28, x_2, x_23);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_3 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_dec(x_8);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec(x_9);
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Server_Watchdog_mainLoop___closed__2;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l___private_Init_Util_0__mkPanicMessage___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_io_error_to_string(x_38);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l_Lean_instInhabitedParserDescr___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = l_IO_throwServerError___rarg(x_49, x_36);
return x_50;
}
}
}
case 1:
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
switch (lean_obj_tag(x_51)) {
case 0:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc(x_55);
lean_dec(x_51);
x_56 = l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1;
x_57 = lean_string_dec_eq(x_54, x_56);
if (x_57 == 0)
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
x_58 = l_Lean_Server_Watchdog_mainLoop___closed__3;
x_59 = l_IO_throwServerError___rarg(x_58, x_52);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_inc(x_2);
x_63 = l_Lean_Server_Watchdog_handleRequest(x_53, x_54, x_62, x_2, x_52);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_2);
x_65 = l_Lean_Server_Watchdog_runClientTask(x_2, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_1 = x_66;
x_3 = x_67;
goto _start;
}
else
{
uint8_t x_69; 
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_65);
if (x_69 == 0)
{
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 0);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_65);
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
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
x_78 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_inc(x_2);
x_79 = l_Lean_Server_Watchdog_handleRequest(x_53, x_54, x_78, x_2, x_52);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_2);
x_81 = l_Lean_Server_Watchdog_runClientTask(x_2, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_1 = x_82;
x_3 = x_83;
goto _start;
}
else
{
uint8_t x_85; 
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_79);
if (x_89 == 0)
{
return x_79;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_79, 0);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_79);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_55);
lean_dec(x_54);
x_93 = l_Lean_Server_Watchdog_shutdown(x_2, x_52);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_2, 1);
lean_inc(x_95);
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_53);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(x_95, x_97, x_94);
lean_dec(x_97);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_53);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_93);
if (x_99 == 0)
{
return x_93;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_93, 0);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_93);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
case 1:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_8, 1);
lean_inc(x_103);
lean_dec(x_8);
x_104 = lean_ctor_get(x_51, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_51, 1);
lean_inc(x_105);
lean_dec(x_51);
x_106 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_107 = lean_string_dec_eq(x_104, x_106);
if (x_107 == 0)
{
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_104);
lean_dec(x_2);
x_108 = l_Lean_Server_Watchdog_mainLoop___closed__3;
x_109 = l_IO_throwServerError___rarg(x_108, x_103);
return x_109;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_dec(x_105);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_inc(x_2);
x_113 = l_Lean_Server_Watchdog_handleNotification(x_104, x_112, x_2, x_103);
lean_dec(x_104);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
lean_inc(x_2);
x_115 = l_Lean_Server_Watchdog_runClientTask(x_2, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_1 = x_116;
x_3 = x_117;
goto _start;
}
else
{
uint8_t x_119; 
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_115);
if (x_119 == 0)
{
return x_115;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_115, 0);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_115);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_113);
if (x_123 == 0)
{
return x_113;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_113, 0);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_113);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_110, 0);
lean_inc(x_127);
lean_dec(x_110);
x_128 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_128, 0, x_127);
lean_inc(x_2);
x_129 = l_Lean_Server_Watchdog_handleNotification(x_104, x_128, x_2, x_103);
lean_dec(x_104);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
lean_inc(x_2);
x_131 = l_Lean_Server_Watchdog_runClientTask(x_2, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_1 = x_132;
x_3 = x_133;
goto _start;
}
else
{
uint8_t x_135; 
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_131);
if (x_135 == 0)
{
return x_131;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_131, 0);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_131);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_129);
if (x_139 == 0)
{
return x_129;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_129, 0);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_129);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
}
else
{
lean_dec(x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_2);
x_143 = l_Lean_Server_Watchdog_mainLoop___closed__3;
x_144 = l_IO_throwServerError___rarg(x_143, x_103);
return x_144;
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_105);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_105, 0);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_148, x_2, x_103);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = l_Lean_Server_Watchdog_findFileWorker(x_154, x_2, x_151);
lean_dec(x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_io_mono_ms_now(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_223; lean_object* x_224; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_2, 6);
lean_inc(x_161);
x_162 = lean_nat_add(x_159, x_161);
lean_dec(x_161);
lean_dec(x_159);
x_163 = lean_ctor_get(x_156, 5);
lean_inc(x_163);
x_223 = lean_st_ref_take(x_163, x_160);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_153);
lean_dec(x_152);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_227 = l_Array_empty___closed__1;
x_228 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_228, 0, x_162);
lean_ctor_set(x_228, 1, x_150);
lean_ctor_set(x_228, 2, x_226);
lean_ctor_set(x_228, 3, x_227);
lean_ctor_set(x_105, 0, x_228);
x_229 = lean_st_ref_set(x_163, x_105, x_225);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = 0;
x_164 = x_231;
x_165 = x_230;
goto block_222;
}
else
{
uint8_t x_232; 
lean_free_object(x_105);
x_232 = !lean_is_exclusive(x_150);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_233 = lean_ctor_get(x_150, 1);
lean_dec(x_233);
x_234 = lean_ctor_get(x_150, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_224);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_224, 0);
x_237 = lean_ctor_get(x_223, 1);
lean_inc(x_237);
lean_dec(x_223);
x_238 = !lean_is_exclusive(x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_239 = lean_ctor_get(x_236, 1);
x_240 = lean_ctor_get(x_236, 3);
lean_dec(x_240);
x_241 = lean_ctor_get(x_236, 0);
lean_dec(x_241);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = l_Array_append___rarg(x_242, x_153);
lean_dec(x_153);
lean_ctor_set(x_150, 1, x_243);
x_244 = l_Array_empty___closed__1;
lean_ctor_set(x_236, 3, x_244);
lean_ctor_set(x_236, 1, x_150);
lean_ctor_set(x_236, 0, x_162);
x_245 = lean_st_ref_set(x_163, x_224, x_237);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = 1;
x_164 = x_247;
x_165 = x_246;
goto block_222;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_248 = lean_ctor_get(x_236, 1);
x_249 = lean_ctor_get(x_236, 2);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_236);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l_Array_append___rarg(x_250, x_153);
lean_dec(x_153);
lean_ctor_set(x_150, 1, x_251);
x_252 = l_Array_empty___closed__1;
x_253 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_253, 0, x_162);
lean_ctor_set(x_253, 1, x_150);
lean_ctor_set(x_253, 2, x_249);
lean_ctor_set(x_253, 3, x_252);
lean_ctor_set(x_224, 0, x_253);
x_254 = lean_st_ref_set(x_163, x_224, x_237);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
lean_dec(x_254);
x_256 = 1;
x_164 = x_256;
x_165 = x_255;
goto block_222;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_257 = lean_ctor_get(x_224, 0);
lean_inc(x_257);
lean_dec(x_224);
x_258 = lean_ctor_get(x_223, 1);
lean_inc(x_258);
lean_dec(x_223);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 2);
lean_inc(x_260);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 x_261 = x_257;
} else {
 lean_dec_ref(x_257);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec(x_259);
x_263 = l_Array_append___rarg(x_262, x_153);
lean_dec(x_153);
lean_ctor_set(x_150, 1, x_263);
x_264 = l_Array_empty___closed__1;
if (lean_is_scalar(x_261)) {
 x_265 = lean_alloc_ctor(0, 4, 0);
} else {
 x_265 = x_261;
}
lean_ctor_set(x_265, 0, x_162);
lean_ctor_set(x_265, 1, x_150);
lean_ctor_set(x_265, 2, x_260);
lean_ctor_set(x_265, 3, x_264);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_267 = lean_st_ref_set(x_163, x_266, x_258);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_269 = 1;
x_164 = x_269;
x_165 = x_268;
goto block_222;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_150);
x_270 = lean_ctor_get(x_224, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_271 = x_224;
} else {
 lean_dec_ref(x_224);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_223, 1);
lean_inc(x_272);
lean_dec(x_223);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 2);
lean_inc(x_274);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 x_275 = x_270;
} else {
 lean_dec_ref(x_270);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = l_Array_append___rarg(x_276, x_153);
lean_dec(x_153);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_152);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_Array_empty___closed__1;
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 4, 0);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_162);
lean_ctor_set(x_280, 1, x_278);
lean_ctor_set(x_280, 2, x_274);
lean_ctor_set(x_280, 3, x_279);
if (lean_is_scalar(x_271)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_271;
}
lean_ctor_set(x_281, 0, x_280);
x_282 = lean_st_ref_set(x_163, x_281, x_272);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = 1;
x_164 = x_284;
x_165 = x_283;
goto block_222;
}
}
block_222:
{
lean_object* x_166; 
x_166 = l_Lean_Server_Watchdog_mainLoop___closed__4;
if (x_164 == 0)
{
lean_object* x_167; 
x_167 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_156, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_st_ref_take(x_163, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_168);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_box(0);
x_174 = lean_st_ref_set(x_163, x_173, x_172);
lean_dec(x_163);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_apply_3(x_166, x_175, x_2, x_176);
return x_177;
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_171);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_171, 0);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
lean_dec(x_170);
x_181 = !lean_is_exclusive(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_179, 2);
lean_dec(x_182);
lean_ctor_set(x_179, 2, x_168);
x_183 = lean_st_ref_set(x_163, x_171, x_180);
lean_dec(x_163);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_apply_3(x_166, x_184, x_2, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_179, 0);
x_188 = lean_ctor_get(x_179, 1);
x_189 = lean_ctor_get(x_179, 3);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_179);
x_190 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
lean_ctor_set(x_190, 2, x_168);
lean_ctor_set(x_190, 3, x_189);
lean_ctor_set(x_171, 0, x_190);
x_191 = lean_st_ref_set(x_163, x_171, x_180);
lean_dec(x_163);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_apply_3(x_166, x_192, x_2, x_193);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_195 = lean_ctor_get(x_171, 0);
lean_inc(x_195);
lean_dec(x_171);
x_196 = lean_ctor_get(x_170, 1);
lean_inc(x_196);
lean_dec(x_170);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_195, 3);
lean_inc(x_199);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_200 = x_195;
} else {
 lean_dec_ref(x_195);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 4, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_197);
lean_ctor_set(x_201, 1, x_198);
lean_ctor_set(x_201, 2, x_168);
lean_ctor_set(x_201, 3, x_199);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = lean_st_ref_set(x_163, x_202, x_196);
lean_dec(x_163);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_apply_3(x_166, x_204, x_2, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_163);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_167);
if (x_207 == 0)
{
return x_167;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_167, 0);
x_209 = lean_ctor_get(x_167, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_167);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_163);
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
x_212 = 10;
x_213 = l_Lean_Server_Watchdog_mainLoop___closed__5;
x_214 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_156, x_211, x_212, x_213, x_165);
lean_dec(x_156);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_apply_3(x_166, x_215, x_2, x_216);
return x_217;
}
else
{
uint8_t x_218; 
lean_dec(x_2);
x_218 = !lean_is_exclusive(x_214);
if (x_218 == 0)
{
return x_214;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_214, 0);
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_214);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_free_object(x_105);
lean_dec(x_2);
x_285 = !lean_is_exclusive(x_158);
if (x_285 == 0)
{
return x_158;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_158, 0);
x_287 = lean_ctor_get(x_158, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_158);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_150);
lean_free_object(x_105);
lean_dec(x_2);
x_289 = !lean_is_exclusive(x_155);
if (x_289 == 0)
{
return x_155;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_155, 0);
x_291 = lean_ctor_get(x_155, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_155);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
uint8_t x_293; 
lean_free_object(x_105);
lean_dec(x_2);
x_293 = !lean_is_exclusive(x_149);
if (x_293 == 0)
{
return x_149;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_149, 0);
x_295 = lean_ctor_get(x_149, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_149);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_146, 0);
lean_inc(x_297);
lean_dec(x_146);
x_298 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_298, x_2, x_103);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 0);
lean_inc(x_304);
x_305 = l_Lean_Server_Watchdog_findFileWorker(x_304, x_2, x_301);
lean_dec(x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_io_mono_ms_now(x_307);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_373; lean_object* x_374; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_ctor_get(x_2, 6);
lean_inc(x_311);
x_312 = lean_nat_add(x_309, x_311);
lean_dec(x_311);
lean_dec(x_309);
x_313 = lean_ctor_get(x_306, 5);
lean_inc(x_313);
x_373 = lean_st_ref_take(x_313, x_310);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
lean_dec(x_303);
lean_dec(x_302);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_377 = l_Array_empty___closed__1;
x_378 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_378, 0, x_312);
lean_ctor_set(x_378, 1, x_300);
lean_ctor_set(x_378, 2, x_376);
lean_ctor_set(x_378, 3, x_377);
lean_ctor_set(x_105, 0, x_378);
x_379 = lean_st_ref_set(x_313, x_105, x_375);
x_380 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
lean_dec(x_379);
x_381 = 0;
x_314 = x_381;
x_315 = x_380;
goto block_372;
}
else
{
uint8_t x_382; 
lean_free_object(x_105);
x_382 = !lean_is_exclusive(x_300);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_383 = lean_ctor_get(x_300, 1);
lean_dec(x_383);
x_384 = lean_ctor_get(x_300, 0);
lean_dec(x_384);
x_385 = !lean_is_exclusive(x_374);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_386 = lean_ctor_get(x_374, 0);
x_387 = lean_ctor_get(x_373, 1);
lean_inc(x_387);
lean_dec(x_373);
x_388 = !lean_is_exclusive(x_386);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_389 = lean_ctor_get(x_386, 1);
x_390 = lean_ctor_get(x_386, 3);
lean_dec(x_390);
x_391 = lean_ctor_get(x_386, 0);
lean_dec(x_391);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = l_Array_append___rarg(x_392, x_303);
lean_dec(x_303);
lean_ctor_set(x_300, 1, x_393);
x_394 = l_Array_empty___closed__1;
lean_ctor_set(x_386, 3, x_394);
lean_ctor_set(x_386, 1, x_300);
lean_ctor_set(x_386, 0, x_312);
x_395 = lean_st_ref_set(x_313, x_374, x_387);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_397 = 1;
x_314 = x_397;
x_315 = x_396;
goto block_372;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_398 = lean_ctor_get(x_386, 1);
x_399 = lean_ctor_get(x_386, 2);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_386);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = l_Array_append___rarg(x_400, x_303);
lean_dec(x_303);
lean_ctor_set(x_300, 1, x_401);
x_402 = l_Array_empty___closed__1;
x_403 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_403, 0, x_312);
lean_ctor_set(x_403, 1, x_300);
lean_ctor_set(x_403, 2, x_399);
lean_ctor_set(x_403, 3, x_402);
lean_ctor_set(x_374, 0, x_403);
x_404 = lean_st_ref_set(x_313, x_374, x_387);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
lean_dec(x_404);
x_406 = 1;
x_314 = x_406;
x_315 = x_405;
goto block_372;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_407 = lean_ctor_get(x_374, 0);
lean_inc(x_407);
lean_dec(x_374);
x_408 = lean_ctor_get(x_373, 1);
lean_inc(x_408);
lean_dec(x_373);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 2);
lean_inc(x_410);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 lean_ctor_release(x_407, 2);
 lean_ctor_release(x_407, 3);
 x_411 = x_407;
} else {
 lean_dec_ref(x_407);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec(x_409);
x_413 = l_Array_append___rarg(x_412, x_303);
lean_dec(x_303);
lean_ctor_set(x_300, 1, x_413);
x_414 = l_Array_empty___closed__1;
if (lean_is_scalar(x_411)) {
 x_415 = lean_alloc_ctor(0, 4, 0);
} else {
 x_415 = x_411;
}
lean_ctor_set(x_415, 0, x_312);
lean_ctor_set(x_415, 1, x_300);
lean_ctor_set(x_415, 2, x_410);
lean_ctor_set(x_415, 3, x_414);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_415);
x_417 = lean_st_ref_set(x_313, x_416, x_408);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = 1;
x_314 = x_419;
x_315 = x_418;
goto block_372;
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
lean_dec(x_300);
x_420 = lean_ctor_get(x_374, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_421 = x_374;
} else {
 lean_dec_ref(x_374);
 x_421 = lean_box(0);
}
x_422 = lean_ctor_get(x_373, 1);
lean_inc(x_422);
lean_dec(x_373);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_420, 2);
lean_inc(x_424);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_425 = x_420;
} else {
 lean_dec_ref(x_420);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
x_427 = l_Array_append___rarg(x_426, x_303);
lean_dec(x_303);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_302);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Array_empty___closed__1;
if (lean_is_scalar(x_425)) {
 x_430 = lean_alloc_ctor(0, 4, 0);
} else {
 x_430 = x_425;
}
lean_ctor_set(x_430, 0, x_312);
lean_ctor_set(x_430, 1, x_428);
lean_ctor_set(x_430, 2, x_424);
lean_ctor_set(x_430, 3, x_429);
if (lean_is_scalar(x_421)) {
 x_431 = lean_alloc_ctor(1, 1, 0);
} else {
 x_431 = x_421;
}
lean_ctor_set(x_431, 0, x_430);
x_432 = lean_st_ref_set(x_313, x_431, x_422);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_434 = 1;
x_314 = x_434;
x_315 = x_433;
goto block_372;
}
}
block_372:
{
lean_object* x_316; 
x_316 = l_Lean_Server_Watchdog_mainLoop___closed__4;
if (x_314 == 0)
{
lean_object* x_317; 
x_317 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_306, x_315);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_st_ref_take(x_313, x_319);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_318);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_box(0);
x_324 = lean_st_ref_set(x_313, x_323, x_322);
lean_dec(x_313);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_apply_3(x_316, x_325, x_2, x_326);
return x_327;
}
else
{
uint8_t x_328; 
x_328 = !lean_is_exclusive(x_321);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_329 = lean_ctor_get(x_321, 0);
x_330 = lean_ctor_get(x_320, 1);
lean_inc(x_330);
lean_dec(x_320);
x_331 = !lean_is_exclusive(x_329);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_329, 2);
lean_dec(x_332);
lean_ctor_set(x_329, 2, x_318);
x_333 = lean_st_ref_set(x_313, x_321, x_330);
lean_dec(x_313);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_apply_3(x_316, x_334, x_2, x_335);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_337 = lean_ctor_get(x_329, 0);
x_338 = lean_ctor_get(x_329, 1);
x_339 = lean_ctor_get(x_329, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_329);
x_340 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
lean_ctor_set(x_340, 2, x_318);
lean_ctor_set(x_340, 3, x_339);
lean_ctor_set(x_321, 0, x_340);
x_341 = lean_st_ref_set(x_313, x_321, x_330);
lean_dec(x_313);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_apply_3(x_316, x_342, x_2, x_343);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_345 = lean_ctor_get(x_321, 0);
lean_inc(x_345);
lean_dec(x_321);
x_346 = lean_ctor_get(x_320, 1);
lean_inc(x_346);
lean_dec(x_320);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_345, 3);
lean_inc(x_349);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_350 = x_345;
} else {
 lean_dec_ref(x_345);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 4, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_318);
lean_ctor_set(x_351, 3, x_349);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
x_353 = lean_st_ref_set(x_313, x_352, x_346);
lean_dec(x_313);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_apply_3(x_316, x_354, x_2, x_355);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_313);
lean_dec(x_2);
x_357 = !lean_is_exclusive(x_317);
if (x_357 == 0)
{
return x_317;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_317, 0);
x_359 = lean_ctor_get(x_317, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_317);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
else
{
lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_313);
x_361 = lean_ctor_get(x_2, 1);
lean_inc(x_361);
x_362 = 10;
x_363 = l_Lean_Server_Watchdog_mainLoop___closed__5;
x_364 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_306, x_361, x_362, x_363, x_315);
lean_dec(x_306);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = lean_apply_3(x_316, x_365, x_2, x_366);
return x_367;
}
else
{
uint8_t x_368; 
lean_dec(x_2);
x_368 = !lean_is_exclusive(x_364);
if (x_368 == 0)
{
return x_364;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_364, 0);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_364);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
}
}
else
{
uint8_t x_435; 
lean_dec(x_306);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_300);
lean_free_object(x_105);
lean_dec(x_2);
x_435 = !lean_is_exclusive(x_308);
if (x_435 == 0)
{
return x_308;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_308, 0);
x_437 = lean_ctor_get(x_308, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_308);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_300);
lean_free_object(x_105);
lean_dec(x_2);
x_439 = !lean_is_exclusive(x_305);
if (x_439 == 0)
{
return x_305;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_305, 0);
x_441 = lean_ctor_get(x_305, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_305);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
uint8_t x_443; 
lean_free_object(x_105);
lean_dec(x_2);
x_443 = !lean_is_exclusive(x_299);
if (x_443 == 0)
{
return x_299;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_299, 0);
x_445 = lean_ctor_get(x_299, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_299);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
}
else
{
lean_object* x_447; 
x_447 = lean_ctor_get(x_105, 0);
lean_inc(x_447);
lean_dec(x_105);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec(x_447);
x_449 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_449, 0, x_448);
x_450 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_449, x_2, x_103);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = lean_ctor_get(x_451, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_451, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
x_456 = l_Lean_Server_Watchdog_findFileWorker(x_455, x_2, x_452);
lean_dec(x_455);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_io_mono_ms_now(x_458);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_508; lean_object* x_509; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_ctor_get(x_2, 6);
lean_inc(x_462);
x_463 = lean_nat_add(x_460, x_462);
lean_dec(x_462);
lean_dec(x_460);
x_464 = lean_ctor_get(x_457, 5);
lean_inc(x_464);
x_508 = lean_st_ref_take(x_464, x_461);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
lean_dec(x_454);
lean_dec(x_453);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_512 = l_Array_empty___closed__1;
x_513 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_513, 0, x_463);
lean_ctor_set(x_513, 1, x_451);
lean_ctor_set(x_513, 2, x_511);
lean_ctor_set(x_513, 3, x_512);
x_514 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_514, 0, x_513);
x_515 = lean_st_ref_set(x_464, x_514, x_510);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_517 = 0;
x_465 = x_517;
x_466 = x_516;
goto block_507;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_518 = x_451;
} else {
 lean_dec_ref(x_451);
 x_518 = lean_box(0);
}
x_519 = lean_ctor_get(x_509, 0);
lean_inc(x_519);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 x_520 = x_509;
} else {
 lean_dec_ref(x_509);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_508, 1);
lean_inc(x_521);
lean_dec(x_508);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_519, 2);
lean_inc(x_523);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 lean_ctor_release(x_519, 2);
 lean_ctor_release(x_519, 3);
 x_524 = x_519;
} else {
 lean_dec_ref(x_519);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_dec(x_522);
x_526 = l_Array_append___rarg(x_525, x_454);
lean_dec(x_454);
if (lean_is_scalar(x_518)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_518;
}
lean_ctor_set(x_527, 0, x_453);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Array_empty___closed__1;
if (lean_is_scalar(x_524)) {
 x_529 = lean_alloc_ctor(0, 4, 0);
} else {
 x_529 = x_524;
}
lean_ctor_set(x_529, 0, x_463);
lean_ctor_set(x_529, 1, x_527);
lean_ctor_set(x_529, 2, x_523);
lean_ctor_set(x_529, 3, x_528);
if (lean_is_scalar(x_520)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_520;
}
lean_ctor_set(x_530, 0, x_529);
x_531 = lean_st_ref_set(x_464, x_530, x_521);
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec(x_531);
x_533 = 1;
x_465 = x_533;
x_466 = x_532;
goto block_507;
}
block_507:
{
lean_object* x_467; 
x_467 = l_Lean_Server_Watchdog_mainLoop___closed__4;
if (x_465 == 0)
{
lean_object* x_468; 
x_468 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_457, x_466);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = lean_st_ref_take(x_464, x_470);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_469);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_474 = lean_box(0);
x_475 = lean_st_ref_set(x_464, x_474, x_473);
lean_dec(x_464);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_apply_3(x_467, x_476, x_2, x_477);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_479 = lean_ctor_get(x_472, 0);
lean_inc(x_479);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_480 = x_472;
} else {
 lean_dec_ref(x_472);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_471, 1);
lean_inc(x_481);
lean_dec(x_471);
x_482 = lean_ctor_get(x_479, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_479, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_479, 3);
lean_inc(x_484);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 lean_ctor_release(x_479, 2);
 lean_ctor_release(x_479, 3);
 x_485 = x_479;
} else {
 lean_dec_ref(x_479);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(0, 4, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_482);
lean_ctor_set(x_486, 1, x_483);
lean_ctor_set(x_486, 2, x_469);
lean_ctor_set(x_486, 3, x_484);
if (lean_is_scalar(x_480)) {
 x_487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_487 = x_480;
}
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_st_ref_set(x_464, x_487, x_481);
lean_dec(x_464);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
x_491 = lean_apply_3(x_467, x_489, x_2, x_490);
return x_491;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_464);
lean_dec(x_2);
x_492 = lean_ctor_get(x_468, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_468, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_494 = x_468;
} else {
 lean_dec_ref(x_468);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_492);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
}
else
{
lean_object* x_496; uint8_t x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_464);
x_496 = lean_ctor_get(x_2, 1);
lean_inc(x_496);
x_497 = 10;
x_498 = l_Lean_Server_Watchdog_mainLoop___closed__5;
x_499 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_457, x_496, x_497, x_498, x_466);
lean_dec(x_457);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_502 = lean_apply_3(x_467, x_500, x_2, x_501);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_2);
x_503 = lean_ctor_get(x_499, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_499, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_505 = x_499;
} else {
 lean_dec_ref(x_499);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_504);
return x_506;
}
}
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_2);
x_534 = lean_ctor_get(x_459, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_459, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_536 = x_459;
} else {
 lean_dec_ref(x_459);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_2);
x_538 = lean_ctor_get(x_456, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_456, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_540 = x_456;
} else {
 lean_dec_ref(x_456);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_538);
lean_ctor_set(x_541, 1, x_539);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_2);
x_542 = lean_ctor_get(x_450, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_450, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_544 = x_450;
} else {
 lean_dec_ref(x_450);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_447, 0);
lean_inc(x_546);
lean_dec(x_447);
x_547 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_547, 0, x_546);
x_548 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_547, x_2, x_103);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 0);
lean_inc(x_553);
x_554 = l_Lean_Server_Watchdog_findFileWorker(x_553, x_2, x_550);
lean_dec(x_553);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_io_mono_ms_now(x_556);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; lean_object* x_564; lean_object* x_606; lean_object* x_607; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get(x_2, 6);
lean_inc(x_560);
x_561 = lean_nat_add(x_558, x_560);
lean_dec(x_560);
lean_dec(x_558);
x_562 = lean_ctor_get(x_555, 5);
lean_inc(x_562);
x_606 = lean_st_ref_take(x_562, x_559);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
lean_dec(x_552);
lean_dec(x_551);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_610 = l_Array_empty___closed__1;
x_611 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_611, 0, x_561);
lean_ctor_set(x_611, 1, x_549);
lean_ctor_set(x_611, 2, x_609);
lean_ctor_set(x_611, 3, x_610);
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_611);
x_613 = lean_st_ref_set(x_562, x_612, x_608);
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
lean_dec(x_613);
x_615 = 0;
x_563 = x_615;
x_564 = x_614;
goto block_605;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_616 = x_549;
} else {
 lean_dec_ref(x_549);
 x_616 = lean_box(0);
}
x_617 = lean_ctor_get(x_607, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_618 = x_607;
} else {
 lean_dec_ref(x_607);
 x_618 = lean_box(0);
}
x_619 = lean_ctor_get(x_606, 1);
lean_inc(x_619);
lean_dec(x_606);
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
x_621 = lean_ctor_get(x_617, 2);
lean_inc(x_621);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 lean_ctor_release(x_617, 3);
 x_622 = x_617;
} else {
 lean_dec_ref(x_617);
 x_622 = lean_box(0);
}
x_623 = lean_ctor_get(x_620, 1);
lean_inc(x_623);
lean_dec(x_620);
x_624 = l_Array_append___rarg(x_623, x_552);
lean_dec(x_552);
if (lean_is_scalar(x_616)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_616;
}
lean_ctor_set(x_625, 0, x_551);
lean_ctor_set(x_625, 1, x_624);
x_626 = l_Array_empty___closed__1;
if (lean_is_scalar(x_622)) {
 x_627 = lean_alloc_ctor(0, 4, 0);
} else {
 x_627 = x_622;
}
lean_ctor_set(x_627, 0, x_561);
lean_ctor_set(x_627, 1, x_625);
lean_ctor_set(x_627, 2, x_621);
lean_ctor_set(x_627, 3, x_626);
if (lean_is_scalar(x_618)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_618;
}
lean_ctor_set(x_628, 0, x_627);
x_629 = lean_st_ref_set(x_562, x_628, x_619);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec(x_629);
x_631 = 1;
x_563 = x_631;
x_564 = x_630;
goto block_605;
}
block_605:
{
lean_object* x_565; 
x_565 = l_Lean_Server_Watchdog_mainLoop___closed__4;
if (x_563 == 0)
{
lean_object* x_566; 
x_566 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_555, x_564);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_st_ref_take(x_562, x_568);
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_567);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_572 = lean_box(0);
x_573 = lean_st_ref_set(x_562, x_572, x_571);
lean_dec(x_562);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_apply_3(x_565, x_574, x_2, x_575);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_577 = lean_ctor_get(x_570, 0);
lean_inc(x_577);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 x_578 = x_570;
} else {
 lean_dec_ref(x_570);
 x_578 = lean_box(0);
}
x_579 = lean_ctor_get(x_569, 1);
lean_inc(x_579);
lean_dec(x_569);
x_580 = lean_ctor_get(x_577, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_577, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_577, 3);
lean_inc(x_582);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 lean_ctor_release(x_577, 2);
 lean_ctor_release(x_577, 3);
 x_583 = x_577;
} else {
 lean_dec_ref(x_577);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(0, 4, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_580);
lean_ctor_set(x_584, 1, x_581);
lean_ctor_set(x_584, 2, x_567);
lean_ctor_set(x_584, 3, x_582);
if (lean_is_scalar(x_578)) {
 x_585 = lean_alloc_ctor(1, 1, 0);
} else {
 x_585 = x_578;
}
lean_ctor_set(x_585, 0, x_584);
x_586 = lean_st_ref_set(x_562, x_585, x_579);
lean_dec(x_562);
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_apply_3(x_565, x_587, x_2, x_588);
return x_589;
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_562);
lean_dec(x_2);
x_590 = lean_ctor_get(x_566, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_566, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_592 = x_566;
} else {
 lean_dec_ref(x_566);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_591);
return x_593;
}
}
else
{
lean_object* x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_562);
x_594 = lean_ctor_get(x_2, 1);
lean_inc(x_594);
x_595 = 10;
x_596 = l_Lean_Server_Watchdog_mainLoop___closed__5;
x_597 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_555, x_594, x_595, x_596, x_564);
lean_dec(x_555);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
x_600 = lean_apply_3(x_565, x_598, x_2, x_599);
return x_600;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_2);
x_601 = lean_ctor_get(x_597, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_597, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 x_603 = x_597;
} else {
 lean_dec_ref(x_597);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
return x_604;
}
}
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
lean_dec(x_555);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_549);
lean_dec(x_2);
x_632 = lean_ctor_get(x_557, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_557, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_634 = x_557;
} else {
 lean_dec_ref(x_557);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_633);
return x_635;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_549);
lean_dec(x_2);
x_636 = lean_ctor_get(x_554, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_554, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_638 = x_554;
} else {
 lean_dec_ref(x_554);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_2);
x_640 = lean_ctor_get(x_548, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_548, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_642 = x_548;
} else {
 lean_dec_ref(x_548);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
}
}
}
}
default: 
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_51);
lean_dec(x_2);
x_644 = lean_ctor_get(x_8, 1);
lean_inc(x_644);
lean_dec(x_8);
x_645 = l_Lean_Server_Watchdog_mainLoop___closed__3;
x_646 = l_IO_throwServerError___rarg(x_645, x_644);
return x_646;
}
}
}
default: 
{
uint8_t x_647; 
lean_dec(x_2);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_8);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_8, 0);
lean_dec(x_648);
x_649 = lean_ctor_get(x_9, 0);
lean_inc(x_649);
lean_dec(x_9);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_649);
return x_8;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_8, 1);
lean_inc(x_650);
lean_dec(x_8);
x_651 = lean_ctor_get(x_9, 0);
lean_inc(x_651);
lean_dec(x_9);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
}
}
else
{
uint8_t x_653; 
lean_dec(x_2);
lean_dec(x_1);
x_653 = !lean_is_exclusive(x_8);
if (x_653 == 0)
{
return x_8;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_8, 0);
x_655 = lean_ctor_get(x_8, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_8);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_mainLoop___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 2;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_SemanticTokenType_names;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2;
x_2 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6;
x_3 = 1;
x_4 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9;
x_5 = lean_alloc_ctor(0, 3, 6);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 4, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 5, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10;
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_7 = lean_string_dec_eq(x_4, x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_6);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_2, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_apply_1(x_3, x_17);
return x_18;
}
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_apply_1(x_3, x_1);
return x_19;
}
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_18 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_17, x_11);
lean_dec(x_11);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l_List_append___rarg(x_23, x_18);
x_25 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = l_Lean_Json_compress(x_27);
x_29 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Char_quote___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_33);
return x_5;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
x_39 = l_List_append___rarg(x_38, x_18);
x_40 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_mkObj(x_41);
x_43 = l_Lean_Json_compress(x_42);
x_44 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Char_quote___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_48);
return x_5;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
x_51 = l_List_append___rarg(x_50, x_18);
x_52 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Json_mkObj(x_53);
x_55 = l_Lean_Json_compress(x_54);
x_56 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Char_quote___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_60);
return x_5;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_dec(x_5);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 2);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_71 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_70, x_64);
lean_dec(x_64);
switch (lean_obj_tag(x_62)) {
case 0:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = l_List_append___rarg(x_76, x_71);
x_78 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = l_Lean_Json_compress(x_80);
x_82 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Char_quote___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_61);
return x_87;
}
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_62, 0);
lean_inc(x_88);
lean_dec(x_62);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_69);
x_93 = l_List_append___rarg(x_92, x_71);
x_94 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Json_mkObj(x_95);
x_97 = l_Lean_Json_compress(x_96);
x_98 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_Char_quote___closed__1;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_61);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_69);
x_106 = l_List_append___rarg(x_105, x_71);
x_107 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_Lean_Json_compress(x_109);
x_111 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Char_quote___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_61);
return x_116;
}
}
}
}
case 1:
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_5);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_5, 0);
lean_dec(x_118);
x_119 = lean_ctor_get(x_6, 0);
lean_inc(x_119);
lean_dec(x_6);
x_120 = lean_string_dec_eq(x_119, x_3);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = l_IO_FS_Stream_readRequestAs___closed__1;
x_122 = lean_string_append(x_121, x_3);
lean_dec(x_3);
x_123 = l_IO_FS_Stream_readRequestAs___closed__2;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_string_append(x_124, x_119);
lean_dec(x_119);
x_126 = l_Char_quote___closed__1;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_128);
return x_5;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_119);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_3);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_5, 0, x_130);
return x_5;
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_5, 1);
lean_inc(x_131);
lean_dec(x_5);
x_132 = lean_ctor_get(x_6, 0);
lean_inc(x_132);
lean_dec(x_6);
x_133 = lean_string_dec_eq(x_132, x_3);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_134 = l_IO_FS_Stream_readRequestAs___closed__1;
x_135 = lean_string_append(x_134, x_3);
lean_dec(x_3);
x_136 = l_IO_FS_Stream_readRequestAs___closed__2;
x_137 = lean_string_append(x_135, x_136);
x_138 = lean_string_append(x_137, x_132);
lean_dec(x_132);
x_139 = l_Char_quote___closed__1;
x_140 = lean_string_append(x_138, x_139);
x_141 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_131);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_132);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_3);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_131);
return x_145;
}
}
}
case 2:
{
uint8_t x_146; 
lean_dec(x_3);
x_146 = !lean_is_exclusive(x_5);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_5, 0);
lean_dec(x_147);
x_148 = lean_ctor_get(x_6, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_6, 1);
lean_inc(x_149);
lean_dec(x_6);
x_150 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
switch (lean_obj_tag(x_148)) {
case 0:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
lean_dec(x_148);
x_155 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
x_159 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Json_mkObj(x_160);
x_162 = l_Lean_Json_compress(x_161);
x_163 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Char_quote___closed__1;
x_166 = lean_string_append(x_164, x_165);
x_167 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_167);
return x_5;
}
case 1:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_168 = lean_ctor_get(x_148, 0);
lean_inc(x_168);
lean_dec(x_148);
x_169 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_153);
x_173 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Lean_Json_mkObj(x_174);
x_176 = l_Lean_Json_compress(x_175);
x_177 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_178 = lean_string_append(x_177, x_176);
lean_dec(x_176);
x_179 = l_Char_quote___closed__1;
x_180 = lean_string_append(x_178, x_179);
x_181 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_181);
return x_5;
}
default: 
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_182 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_153);
x_184 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = l_Lean_Json_mkObj(x_185);
x_187 = l_Lean_Json_compress(x_186);
x_188 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Char_quote___closed__1;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_192);
return x_5;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_5, 1);
lean_inc(x_193);
lean_dec(x_5);
x_194 = lean_ctor_get(x_6, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_6, 1);
lean_inc(x_195);
lean_dec(x_6);
x_196 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
switch (lean_obj_tag(x_194)) {
case 0:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_200 = lean_ctor_get(x_194, 0);
lean_inc(x_200);
lean_dec(x_194);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_199);
x_205 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_Json_mkObj(x_206);
x_208 = l_Lean_Json_compress(x_207);
x_209 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_210 = lean_string_append(x_209, x_208);
lean_dec(x_208);
x_211 = l_Char_quote___closed__1;
x_212 = lean_string_append(x_210, x_211);
x_213 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_193);
return x_214;
}
case 1:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_215 = lean_ctor_get(x_194, 0);
lean_inc(x_215);
lean_dec(x_194);
x_216 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_199);
x_220 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l_Lean_Json_mkObj(x_221);
x_223 = l_Lean_Json_compress(x_222);
x_224 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_225 = lean_string_append(x_224, x_223);
lean_dec(x_223);
x_226 = l_Char_quote___closed__1;
x_227 = lean_string_append(x_225, x_226);
x_228 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_193);
return x_229;
}
default: 
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_230 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_199);
x_232 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l_Lean_Json_mkObj(x_233);
x_235 = l_Lean_Json_compress(x_234);
x_236 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_237 = lean_string_append(x_236, x_235);
lean_dec(x_235);
x_238 = l_Char_quote___closed__1;
x_239 = lean_string_append(x_237, x_238);
x_240 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_193);
return x_241;
}
}
}
}
default: 
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_3);
x_242 = lean_ctor_get(x_5, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_243 = x_5;
} else {
 lean_dec_ref(x_5);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_6, 0);
lean_inc(x_244);
x_245 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_246 = lean_ctor_get(x_6, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_6, 2);
lean_inc(x_247);
lean_dec(x_6);
x_248 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_248, 0, x_246);
x_249 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_254 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_253, x_247);
lean_dec(x_247);
switch (lean_obj_tag(x_244)) {
case 0:
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_244, 0);
lean_inc(x_291);
lean_dec(x_244);
x_292 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_255 = x_292;
goto block_290;
}
case 1:
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_244, 0);
lean_inc(x_293);
lean_dec(x_244);
x_294 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_255 = x_294;
goto block_290;
}
default: 
{
lean_object* x_295; 
x_295 = lean_box(0);
x_255 = x_295;
goto block_290;
}
}
block_290:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
switch (x_245) {
case 0:
{
lean_object* x_279; 
x_279 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_258 = x_279;
goto block_278;
}
case 1:
{
lean_object* x_280; 
x_280 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_258 = x_280;
goto block_278;
}
case 2:
{
lean_object* x_281; 
x_281 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_258 = x_281;
goto block_278;
}
case 3:
{
lean_object* x_282; 
x_282 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_258 = x_282;
goto block_278;
}
case 4:
{
lean_object* x_283; 
x_283 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_258 = x_283;
goto block_278;
}
case 5:
{
lean_object* x_284; 
x_284 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_258 = x_284;
goto block_278;
}
case 6:
{
lean_object* x_285; 
x_285 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_258 = x_285;
goto block_278;
}
case 7:
{
lean_object* x_286; 
x_286 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_258 = x_286;
goto block_278;
}
case 8:
{
lean_object* x_287; 
x_287 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_258 = x_287;
goto block_278;
}
case 9:
{
lean_object* x_288; 
x_288 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_258 = x_288;
goto block_278;
}
default: 
{
lean_object* x_289; 
x_289 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_258 = x_289;
goto block_278;
}
}
block_278:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_259 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
x_262 = l_List_append___rarg(x_261, x_254);
x_263 = l_Lean_Json_mkObj(x_262);
x_264 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_251);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lean_Json_mkObj(x_269);
x_271 = l_Lean_Json_compress(x_270);
x_272 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_273 = lean_string_append(x_272, x_271);
lean_dec(x_271);
x_274 = l_Char_quote___closed__1;
x_275 = lean_string_append(x_273, x_274);
x_276 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_276, 0, x_275);
if (lean_is_scalar(x_243)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_243;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_242);
return x_277;
}
}
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_3);
x_296 = !lean_is_exclusive(x_5);
if (x_296 == 0)
{
return x_5;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_5, 0);
x_298 = lean_ctor_get(x_5, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_5);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
}
lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(x_1, x_5, x_2, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_instInhabitedParserDescr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_instInhabitedParserDescr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_instInhabitedParserDescr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("initialized");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected an exit notification");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_16 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1;
lean_inc(x_3);
x_17 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(x_3, x_16, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_1);
x_19 = l_Lean_Server_Watchdog_runClientTask(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
x_22 = l_Lean_Server_Watchdog_mainLoop(x_20, x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_IO_FS_Stream_readLspMessage(x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_32 = lean_string_dec_eq(x_29, x_31);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_free_object(x_24);
x_33 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_34 = l_IO_throwServerError___rarg(x_33, x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_4 = x_35;
x_5 = x_36;
goto block_15;
}
else
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_30);
lean_free_object(x_24);
x_38 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_39 = l_IO_throwServerError___rarg(x_38, x_27);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_4 = x_40;
x_5 = x_41;
goto block_15;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
x_45 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_46 = lean_string_dec_eq(x_43, x_45);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
x_47 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_48 = l_IO_throwServerError___rarg(x_47, x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_4 = x_49;
x_5 = x_50;
goto block_15;
}
else
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
x_53 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_54 = l_IO_throwServerError___rarg(x_53, x_42);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_4 = x_55;
x_5 = x_56;
goto block_15;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_25);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_dec(x_24);
x_58 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_59 = l_IO_throwServerError___rarg(x_58, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_4 = x_60;
x_5 = x_61;
goto block_15;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_24, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_dec(x_24);
x_4 = x_62;
x_5 = x_63;
goto block_15;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_dec(x_22);
x_4 = x_64;
x_5 = x_65;
goto block_15;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
lean_dec(x_19);
x_4 = x_66;
x_5 = x_67;
goto block_15;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_17, 1);
lean_inc(x_69);
lean_dec(x_17);
x_4 = x_68;
x_5 = x_69;
goto block_15;
}
block_15:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Watchdog_shutdown(x_1, x_5);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
}
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_initAndRunWatchdog_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_string_dec_eq(x_10, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
x_13 = l_IO_FS_Stream_readRequestAs___closed__1;
x_14 = lean_string_append(x_13, x_3);
lean_dec(x_3);
x_15 = l_IO_FS_Stream_readRequestAs___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
x_18 = l_Char_quote___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_8;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_22 = x_47;
goto block_46;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
lean_dec(x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_22 = x_50;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_22 = x_52;
goto block_46;
}
}
block_46:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__1;
x_24 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_22, x_23);
x_25 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__2;
x_26 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_22, x_25);
x_27 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__3;
x_28 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_22, x_27);
x_29 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__4;
x_30 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(x_22, x_29);
x_31 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__9;
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_22, x_31);
x_33 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_225____closed__8;
x_34 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(x_22, x_33);
lean_dec(x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_37);
if (lean_is_scalar(x_8)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_8;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_26);
lean_ctor_set(x_42, 2, x_28);
lean_ctor_set(x_42, 3, x_30);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_34);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*6, x_43);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_42);
if (lean_is_scalar(x_8)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_8;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
}
}
}
case 1:
{
uint8_t x_53; 
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_54 = lean_ctor_get(x_5, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_61 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_60, x_56);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Json_mkObj(x_64);
x_66 = l_Lean_Json_compress(x_65);
x_67 = l_IO_FS_Stream_readRequestAs___closed__5;
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = l_Char_quote___closed__1;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_71);
return x_5;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_72 = lean_ctor_get(x_5, 1);
lean_inc(x_72);
lean_dec(x_5);
x_73 = lean_ctor_get(x_6, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_79 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_78, x_74);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Json_mkObj(x_82);
x_84 = l_Lean_Json_compress(x_83);
x_85 = l_IO_FS_Stream_readRequestAs___closed__5;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = l_Char_quote___closed__1;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_72);
return x_90;
}
}
case 2:
{
uint8_t x_91; 
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_5);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_5, 0);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_6, 1);
lean_inc(x_94);
lean_dec(x_6);
x_95 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
switch (lean_obj_tag(x_93)) {
case 0:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
x_104 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_Json_mkObj(x_105);
x_107 = l_Lean_Json_compress(x_106);
x_108 = l_IO_FS_Stream_readRequestAs___closed__5;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = l_Char_quote___closed__1;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_112);
return x_5;
}
case 1:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_113 = lean_ctor_get(x_93, 0);
lean_inc(x_113);
lean_dec(x_93);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_98);
x_118 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_Json_mkObj(x_119);
x_121 = l_Lean_Json_compress(x_120);
x_122 = l_IO_FS_Stream_readRequestAs___closed__5;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = l_Char_quote___closed__1;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_126);
return x_5;
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_127 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_98);
x_129 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Json_mkObj(x_130);
x_132 = l_Lean_Json_compress(x_131);
x_133 = l_IO_FS_Stream_readRequestAs___closed__5;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Char_quote___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_137);
return x_5;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_5, 1);
lean_inc(x_138);
lean_dec(x_5);
x_139 = lean_ctor_get(x_6, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_6, 1);
lean_inc(x_140);
lean_dec(x_6);
x_141 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
switch (lean_obj_tag(x_139)) {
case 0:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_145 = lean_ctor_get(x_139, 0);
lean_inc(x_145);
lean_dec(x_139);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_144);
x_150 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = l_Lean_Json_mkObj(x_151);
x_153 = l_Lean_Json_compress(x_152);
x_154 = l_IO_FS_Stream_readRequestAs___closed__5;
x_155 = lean_string_append(x_154, x_153);
lean_dec(x_153);
x_156 = l_Char_quote___closed__1;
x_157 = lean_string_append(x_155, x_156);
x_158 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_138);
return x_159;
}
case 1:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_160 = lean_ctor_get(x_139, 0);
lean_inc(x_160);
lean_dec(x_139);
x_161 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_144);
x_165 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Json_mkObj(x_166);
x_168 = l_Lean_Json_compress(x_167);
x_169 = l_IO_FS_Stream_readRequestAs___closed__5;
x_170 = lean_string_append(x_169, x_168);
lean_dec(x_168);
x_171 = l_Char_quote___closed__1;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_138);
return x_174;
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_175 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_144);
x_177 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = l_Lean_Json_mkObj(x_178);
x_180 = l_Lean_Json_compress(x_179);
x_181 = l_IO_FS_Stream_readRequestAs___closed__5;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
x_183 = l_Char_quote___closed__1;
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_138);
return x_186;
}
}
}
}
default: 
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_3);
x_187 = lean_ctor_get(x_5, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_188 = x_5;
} else {
 lean_dec_ref(x_5);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_6, 0);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_191 = lean_ctor_get(x_6, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_6, 2);
lean_inc(x_192);
lean_dec(x_6);
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_191);
x_194 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_199 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_198, x_192);
lean_dec(x_192);
switch (lean_obj_tag(x_189)) {
case 0:
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_189, 0);
lean_inc(x_236);
lean_dec(x_189);
x_237 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_200 = x_237;
goto block_235;
}
case 1:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_189, 0);
lean_inc(x_238);
lean_dec(x_189);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_200 = x_239;
goto block_235;
}
default: 
{
lean_object* x_240; 
x_240 = lean_box(0);
x_200 = x_240;
goto block_235;
}
}
block_235:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
switch (x_190) {
case 0:
{
lean_object* x_224; 
x_224 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_203 = x_224;
goto block_223;
}
case 1:
{
lean_object* x_225; 
x_225 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_203 = x_225;
goto block_223;
}
case 2:
{
lean_object* x_226; 
x_226 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_203 = x_226;
goto block_223;
}
case 3:
{
lean_object* x_227; 
x_227 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_203 = x_227;
goto block_223;
}
case 4:
{
lean_object* x_228; 
x_228 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_203 = x_228;
goto block_223;
}
case 5:
{
lean_object* x_229; 
x_229 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_203 = x_229;
goto block_223;
}
case 6:
{
lean_object* x_230; 
x_230 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_203 = x_230;
goto block_223;
}
case 7:
{
lean_object* x_231; 
x_231 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_203 = x_231;
goto block_223;
}
case 8:
{
lean_object* x_232; 
x_232 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_203 = x_232;
goto block_223;
}
case 9:
{
lean_object* x_233; 
x_233 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_203 = x_233;
goto block_223;
}
default: 
{
lean_object* x_234; 
x_234 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_203 = x_234;
goto block_223;
}
}
block_223:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_204 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_197);
x_207 = l_List_append___rarg(x_206, x_199);
x_208 = l_Lean_Json_mkObj(x_207);
x_209 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_196);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = l_Lean_Json_mkObj(x_214);
x_216 = l_Lean_Json_compress(x_215);
x_217 = l_IO_FS_Stream_readRequestAs___closed__5;
x_218 = lean_string_append(x_217, x_216);
lean_dec(x_216);
x_219 = l_Char_quote___closed__1;
x_220 = lean_string_append(x_218, x_219);
x_221 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_221, 0, x_220);
if (lean_is_scalar(x_188)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_188;
 lean_ctor_set_tag(x_222, 1);
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_187);
return x_222;
}
}
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_5);
if (x_241 == 0)
{
return x_5;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_5, 0);
x_243 = lean_ctor_get(x_5, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_5);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(x_1, x_5, x_2, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_instInhabitedParserDescr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_instInhabitedParserDescr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_instInhabitedParserDescr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_457_(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wdIn.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wdOut.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wdErr.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("0.0.1");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_msgToDiagnostic___closed__1;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_box(0);
x_9 = l_IO_mkRef___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1;
x_13 = 0;
x_14 = l_Lean_Server_maybeTee(x_12, x_13, x_1, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2;
x_18 = 1;
x_19 = l_Lean_Server_maybeTee(x_17, x_18, x_2, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3;
x_23 = l_Lean_Server_maybeTee(x_22, x_18, x_3, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Parser_Command_initialize___elambda__1___closed__1;
lean_inc(x_15);
x_27 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(x_15, x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_20);
x_34 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(x_20, x_33, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 3);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(200u);
x_38 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_20);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_4);
lean_ctor_set(x_38, 4, x_10);
lean_ctor_set(x_38, 5, x_31);
lean_ctor_set(x_38, 6, x_37);
lean_ctor_set(x_38, 7, x_5);
x_39 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_38, x_36);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_unsigned_to_nat(200u);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_20);
lean_ctor_set(x_43, 2, x_24);
lean_ctor_set(x_43, 3, x_4);
lean_ctor_set(x_43, 4, x_10);
lean_ctor_set(x_43, 5, x_31);
lean_ctor_set(x_43, 6, x_42);
lean_ctor_set(x_43, 7, x_5);
x_44 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_43, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_47, 0, x_15);
lean_ctor_set(x_47, 1, x_20);
lean_ctor_set(x_47, 2, x_24);
lean_ctor_set(x_47, 3, x_4);
lean_ctor_set(x_47, 4, x_10);
lean_ctor_set(x_47, 5, x_31);
lean_ctor_set(x_47, 6, x_46);
lean_ctor_set(x_47, 7, x_5);
x_48 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_47, x_45);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_27);
if (x_53 == 0)
{
return x_27;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_27, 0);
x_55 = lean_ctor_get(x_27, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_27);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_23);
if (x_57 == 0)
{
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_14);
if (x_65 == 0)
{
return x_14;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_14, 0);
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_14);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_WORKER_PATH");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1;
x_9 = lean_io_getenv(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(x_1, x_2, x_3, x_4, x_5, x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(x_1, x_2, x_3, x_4, x_15, x_16, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_SYSROOT");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/bin/lean");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_app_dir(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1;
x_10 = lean_io_getenv(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(x_2, x_3, x_4, x_1, x_7, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_instInhabitedParserDescr___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_System_FilePath_exeSuffix;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_17);
x_24 = lean_box(0);
x_25 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(x_2, x_3, x_4, x_1, x_23, x_24, x_15);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_IO_getStdin___at_Lean_Server_Watchdog_watchdogMain___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin(x_1);
return x_2;
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_watchdogMain___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 10;
x_6 = lean_string_push(x_2, x_5);
x_7 = lean_apply_2(x_4, x_6, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Watchdog error: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* lean_server_watchdog_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_stdin(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Server_Watchdog_initAndRunWatchdog(x_1, x_4, x_7, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_io_error_to_string(x_19);
x_22 = l_Lean_Server_Watchdog_watchdogMain___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_instInhabitedParserDescr___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_watchdogMain___spec__2(x_10, x_25, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_6);
if (x_41 == 0)
{
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Data_ByteArray(lean_object*);
lean_object* initialize_Std_Data_RBMap(lean_object*);
lean_object* initialize_Lean_Elab_Import(lean_object*);
lean_object* initialize_Lean_Data_Lsp(lean_object*);
lean_object* initialize_Lean_Server_FileSource(lean_object*);
lean_object* initialize_Lean_Server_Utils(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_Watchdog(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileSource(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Watchdog_workerCfg = _init_l_Lean_Server_Watchdog_workerCfg();
lean_mark_persistent(l_Lean_Server_Watchdog_workerCfg);
l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1 = _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1);
l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1 = _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1);
l_Lean_Server_Watchdog_findFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_findFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_findFileWorker___closed__1);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8);
l_Lean_Server_Watchdog_startFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__1);
l_Lean_Server_Watchdog_startFileWorker___closed__2 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__2);
l_Lean_Server_Watchdog_startFileWorker___closed__3 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__3);
l_Lean_Server_Watchdog_startFileWorker___closed__4 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__4);
l_Lean_Server_Watchdog_startFileWorker___closed__5 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__5);
l_Lean_Server_Watchdog_terminateFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_terminateFileWorker___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1();
l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2();
l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1);
l_Lean_Server_Watchdog_handleEdits___closed__1 = _init_l_Lean_Server_Watchdog_handleEdits___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___closed__1);
l_Lean_Server_Watchdog_handleEdits___closed__2 = _init_l_Lean_Server_Watchdog_handleEdits___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___closed__2);
l_Lean_Server_Watchdog_handleEdits___closed__3 = _init_l_Lean_Server_Watchdog_handleEdits___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___closed__3);
l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1 = _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1);
l_Lean_Server_Watchdog_parseParams___rarg___closed__1 = _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_parseParams___rarg___closed__1);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__1);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__2);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__3);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__4);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__5);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__6);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__7);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__8);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__9);
l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10 = _init_l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__2___rarg___closed__10);
l_Lean_Server_Watchdog_handleRequest___closed__1 = _init_l_Lean_Server_Watchdog_handleRequest___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__1);
l_Lean_Server_Watchdog_handleRequest___closed__2 = _init_l_Lean_Server_Watchdog_handleRequest___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__2);
l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1 = _init_l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1);
l_Lean_Server_Watchdog_handleNotification___closed__1 = _init_l_Lean_Server_Watchdog_handleNotification___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__1);
l_Lean_Server_Watchdog_handleNotification___closed__2 = _init_l_Lean_Server_Watchdog_handleNotification___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__2);
l_Lean_Server_Watchdog_runClientTask___closed__1 = _init_l_Lean_Server_Watchdog_runClientTask___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_runClientTask___closed__1);
l_Lean_Server_Watchdog_runClientTask___closed__2 = _init_l_Lean_Server_Watchdog_runClientTask___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_runClientTask___closed__2);
l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1 = _init_l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1);
l_Lean_Server_Watchdog_mainLoop___closed__1 = _init_l_Lean_Server_Watchdog_mainLoop___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__1);
l_Lean_Server_Watchdog_mainLoop___closed__2 = _init_l_Lean_Server_Watchdog_mainLoop___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__2);
l_Lean_Server_Watchdog_mainLoop___closed__3 = _init_l_Lean_Server_Watchdog_mainLoop___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__3);
l_Lean_Server_Watchdog_mainLoop___closed__4 = _init_l_Lean_Server_Watchdog_mainLoop___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__4);
l_Lean_Server_Watchdog_mainLoop___closed__5 = _init_l_Lean_Server_Watchdog_mainLoop___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__5);
l_Lean_Server_Watchdog_mainLoop___closed__6 = _init_l_Lean_Server_Watchdog_mainLoop___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__6);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10);
l_Lean_Server_Watchdog_mkLeanServerCapabilities = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2);
l_Lean_Server_Watchdog_watchdogMain___closed__1 = _init_l_Lean_Server_Watchdog_watchdogMain___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_watchdogMain___closed__1);
l_Lean_Server_Watchdog_watchdogMain___boxed__const__1 = _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__1();
lean_mark_persistent(l_Lean_Server_Watchdog_watchdogMain___boxed__const__1);
l_Lean_Server_Watchdog_watchdogMain___boxed__const__2 = _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__2();
lean_mark_persistent(l_Lean_Server_Watchdog_watchdogMain___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

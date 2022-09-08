// Lean compiler output
// Module: Lean.Server.Watchdog
// Imports: Init Init.System.IO Init.Data.ByteArray Lean.Data.RBMap Lean.Elab.Import Lean.Util.Paths Lean.Data.FuzzyMatching Lean.Data.Json Lean.Data.Lsp Lean.Server.Utils Lean.Server.Requests Lean.Server.References
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
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__10;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__18;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__15;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__32;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
static lean_object* l_Lean_Server_Watchdog_handleNotification___closed__6;
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__9___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_startFileWorker(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__52;
extern lean_object* l_String_instInhabitedString;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_loadReferences___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__29;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__28;
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_934_(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__17;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__8;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__14;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5(lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__1;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_146_(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__5;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_2069_(lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidOpen(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleRequest___closed__1;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__30;
lean_object* lean_io_wait_any(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__8;
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
static lean_object* l_Lean_Server_Watchdog_handleRequest___closed__2;
static lean_object* l_Lean_Server_Watchdog_handleNotification___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__8(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker___boxed(lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__3;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__2;
extern lean_object* l_Lean_Lsp_SemanticTokenModifier_names;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_969_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__3(lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__5;
static lean_object* l_Lean_Server_Watchdog_terminateFileWorker___closed__2;
static lean_object* l_Lean_Server_Watchdog_handleNotification___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__56;
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__9;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_searchPathRef;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findDefinitions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleEdits___closed__3;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__50;
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2;
lean_object* lean_private_to_user_name(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__53;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_shutdown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_eraseFileWorker___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_erasePendingRequest(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__24;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__63;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
static lean_object* l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__9;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__49;
lean_object* l_Lean_Server_publishProgressAtPos(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__4;
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_loadReferences(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonDidChangeWatchedFilesRegistrationOptions____x40_Lean_Data_Lsp_Workspace___hyg_304_(lean_object*);
lean_object* l_Lean_Server_References_definitionsMatching___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux(lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleNotification___closed__2;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__2;
lean_object* l_Array_qpartition_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__3(size_t, size_t, lean_object*);
lean_object* l_IO_throwServerError___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__8;
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__9;
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__7;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__34;
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__3___boxed(lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__4;
extern lean_object* l_Lean_Lsp_SemanticTokenType_names;
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__48;
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__21;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__38;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__22;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleReference___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__4;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__3;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__10;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__6;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleReference___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_workerCfg;
lean_object* l_Lean_Server_References_referringTo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_findDefinitions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8;
static lean_object* l_Lean_Server_Watchdog_findDefinitions___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__16;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4;
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__1;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__33;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__16;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
lean_object* l_Lean_Server_References_removeIlean(lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9;
static lean_object* l_Lean_Server_Watchdog_runClientTask___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidClose(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_findWorkerPath___closed__3;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_dedicated;
lean_object* l_Lean_Server_routeLspRequest(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedFloat;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__54;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__62;
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_runClientTask___closed__2;
uint8_t lean_float_decLt(double, double);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__11___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__2;
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_References_addIlean(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__4;
static lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_mainLoop___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__2;
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_eraseFileWorker(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__11;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findDefinitions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidClose___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_References_updateWorkerRefs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__19;
lean_object* l_Std_RBNode_appendTrees___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__46;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_1512_(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__1;
lean_object* l_Lean_Server_Ilean_load(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1___closed__1;
uint8_t l_Std_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_1366_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_83_(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1___boxed(lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_erasePendingRequest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__17;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2(lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleCrash(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoFinal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__60;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__47;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardRequestToWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleReference(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__35;
lean_object* l_Lean_Server_References_removeWorkerRefs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__36;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_stdout(lean_object*);
lean_object* l_Lean_initSrcSearchPath___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__7;
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_server_watchdog_main(lean_object*, lean_object*);
static uint8_t l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__64;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__3;
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_112_(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__6;
lean_object* lean_get_prefix(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonSymbolInformation____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3319_(lean_object*);
lean_object* l_Std_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_mainLoop(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__5;
lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonDidChangeWatchedFilesParams____x40_Lean_Data_Lsp_Workspace___hyg_575_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoUpdate(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleNotification(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidCloseTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_649_(lean_object*);
lean_object* l_Lean_Server_References_finalizeWorkerRefs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__25;
static lean_object* l_Lean_Server_Watchdog_handleEdits___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__11(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__23;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__41;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__13;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_References_findAt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__2;
static lean_object* l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__6;
static lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__1;
static lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1;
static lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__44;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__10;
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__6;
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__20;
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
static lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__2;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__1;
static lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_shutdown(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1;
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__10;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities;
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__2;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isEmpty(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst___closed__1;
lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__5;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__39;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__21;
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__13;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__45;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__40;
static lean_object* l_Lean_Server_Watchdog_handleNotification___closed__5;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__9;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__27;
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__3;
extern lean_object* l_Lean_Lsp_instInhabitedLocation;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__15;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_1442_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_431_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findDefinitions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__7;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__58;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__26;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_loadReferences___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__11;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_watchdogMain___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_findDefinitions___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_stdin(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleEdits___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__59;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_updateFileWorkers(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__31;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleCrash___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_1570_(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__4;
static lean_object* l_Lean_Server_Watchdog_findWorkerPath___closed__2;
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__7;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__12;
static lean_object* l_Lean_Server_Watchdog_findWorkerPath___closed__1;
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_117_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_172_(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoUpdate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__2;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__57;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_app_path(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_updateFileWorkers___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidChangeWatchedFiles(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__19;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__51;
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_findFileWorker_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mainLoop___closed__7;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Server_References_empty;
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__61;
lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__20;
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__5;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleCancelRequest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__14;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_log(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__12___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__3;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_471_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1009_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__10(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__43;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath(lean_object*);
static lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__18;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_400_(lean_object*);
static lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__12;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_workerCfg___closed__1;
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1;
static lean_object* l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonReferenceParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2432_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_References_definitionOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__6(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_827_(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1;
static uint8_t l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1;
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonWorkspaceSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2570_(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleNotification___closed__3;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_708_(lean_object*);
static lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__6;
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__42;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__6;
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__37;
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed(lean_object*);
static lean_object* l_Lean_Server_Watchdog_tryWriteMessage___closed__55;
static lean_object* _init_l_Lean_Server_Watchdog_workerCfg___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_workerCfg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Watchdog_workerCfg___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<input>", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_stdin(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_stdout(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_5);
x_14 = l_Std_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_8);
x_20 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_22);
lean_inc(x_1);
x_25 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Std_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_21);
x_31 = l_Std_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_32 = l_Std_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Std_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_24);
x_38 = l_Std_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_erasePendingRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 4);
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_erasePendingRequest___spec__1(x_2, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_erasePendingRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_FileWorker_erasePendingRequest(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Internal error: empty grouped edits reference in signal task", 60);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_io_mono_ms_now(x_2);
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
lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
x_18 = lean_nat_sub(x_16, x_4);
lean_dec(x_4);
lean_dec(x_16);
x_19 = lean_uint32_of_nat(x_18);
lean_dec(x_18);
x_20 = l_IO_sleep(x_19, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_2 = x_21;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_4);
x_23 = lean_box(0);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_nat_dec_le(x_26, x_4);
if (x_27 == 0)
{
lean_object* x_28; uint32_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_nat_sub(x_26, x_4);
lean_dec(x_4);
lean_dec(x_26);
x_29 = lean_uint32_of_nat(x_28);
lean_dec(x_28);
x_30 = l_IO_sleep(x_29, x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_2 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Task_Priority_default;
x_6 = lean_io_as_task(x_4, x_5, x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_10 = lean_task_map(x_9, x_8, x_5);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_14 = lean_task_map(x_13, x_11, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = lean_string_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
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
x_25 = lean_string_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
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
x_40 = lean_string_dec_eq(x_2, x_36);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Std_RBNode_isRed___rarg(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_38, x_2, x_3);
x_43 = 1;
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_38, x_2, x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = 0;
lean_ctor_set(x_44, 0, x_46);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_50);
x_51 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_51);
return x_1;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_44, 1);
x_53 = lean_ctor_get(x_44, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = 0;
x_55 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_54);
x_56 = 1;
lean_ctor_set(x_1, 3, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_44, 1);
x_60 = lean_ctor_get(x_44, 2);
x_61 = lean_ctor_get(x_44, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_44, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_46);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
x_66 = lean_ctor_get(x_46, 2);
x_67 = lean_ctor_get(x_46, 3);
x_68 = 1;
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_68);
lean_ctor_set(x_44, 3, x_67);
lean_ctor_set(x_44, 2, x_66);
lean_ctor_set(x_44, 1, x_65);
lean_ctor_set(x_44, 0, x_64);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_68);
x_69 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_46, 0);
x_71 = lean_ctor_get(x_46, 1);
x_72 = lean_ctor_get(x_46, 2);
x_73 = lean_ctor_get(x_46, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_46);
x_74 = 1;
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_35);
lean_ctor_set(x_75, 1, x_36);
lean_ctor_set(x_75, 2, x_37);
lean_ctor_set(x_75, 3, x_45);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
lean_ctor_set(x_44, 3, x_73);
lean_ctor_set(x_44, 2, x_72);
lean_ctor_set(x_44, 1, x_71);
lean_ctor_set(x_44, 0, x_70);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_74);
x_76 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_76);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_44, 1);
x_78 = lean_ctor_get(x_44, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_44);
x_79 = lean_ctor_get(x_46, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_46, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_46, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_46, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_83 = x_46;
} else {
 lean_dec_ref(x_46);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_45);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
x_87 = 0;
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_44);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_44, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_44, 0);
lean_dec(x_90);
x_91 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_91);
x_92 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_44, 1);
x_94 = lean_ctor_get(x_44, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_44);
x_95 = 0;
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_45);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_46);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
x_97 = 1;
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
}
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_44, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_45);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_45, 0);
x_103 = lean_ctor_get(x_45, 1);
x_104 = lean_ctor_get(x_45, 2);
x_105 = lean_ctor_get(x_45, 3);
x_106 = 1;
lean_ctor_set(x_45, 3, x_102);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_106);
lean_ctor_set(x_44, 0, x_105);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_106);
x_107 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_107);
return x_1;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_ctor_get(x_45, 0);
x_109 = lean_ctor_get(x_45, 1);
x_110 = lean_ctor_get(x_45, 2);
x_111 = lean_ctor_get(x_45, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_45);
x_112 = 1;
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_35);
lean_ctor_set(x_113, 1, x_36);
lean_ctor_set(x_113, 2, x_37);
lean_ctor_set(x_113, 3, x_108);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
lean_ctor_set(x_44, 0, x_111);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_112);
x_114 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_110);
lean_ctor_set(x_1, 1, x_109);
lean_ctor_set(x_1, 0, x_113);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_114);
return x_1;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_115 = lean_ctor_get(x_44, 1);
x_116 = lean_ctor_get(x_44, 2);
x_117 = lean_ctor_get(x_44, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_44);
x_118 = lean_ctor_get(x_45, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_45, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_45, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_45, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_122 = x_45;
} else {
 lean_dec_ref(x_45);
 x_122 = lean_box(0);
}
x_123 = 1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(1, 4, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_35);
lean_ctor_set(x_124, 1, x_36);
lean_ctor_set(x_124, 2, x_37);
lean_ctor_set(x_124, 3, x_118);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_123);
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_115);
lean_ctor_set(x_125, 2, x_116);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_123);
x_126 = 0;
lean_ctor_set(x_1, 3, x_125);
lean_ctor_set(x_1, 2, x_120);
lean_ctor_set(x_1, 1, x_119);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_126);
return x_1;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_44, 3);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_44);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_44, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_44, 0);
lean_dec(x_130);
x_131 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_131);
x_132 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_132);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_44, 1);
x_134 = lean_ctor_get(x_44, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_44);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_45);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
x_137 = 1;
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
uint8_t x_138; 
x_138 = lean_ctor_get_uint8(x_127, sizeof(void*)*4);
if (x_138 == 0)
{
uint8_t x_139; 
lean_free_object(x_1);
x_139 = !lean_is_exclusive(x_44);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_44, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_44, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_127);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_127, 0);
x_144 = lean_ctor_get(x_127, 1);
x_145 = lean_ctor_get(x_127, 2);
x_146 = lean_ctor_get(x_127, 3);
x_147 = 1;
lean_inc(x_45);
lean_ctor_set(x_127, 3, x_45);
lean_ctor_set(x_127, 2, x_37);
lean_ctor_set(x_127, 1, x_36);
lean_ctor_set(x_127, 0, x_35);
x_148 = !lean_is_exclusive(x_45);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_45, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_45, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_45, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_45, 0);
lean_dec(x_152);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
lean_ctor_set(x_45, 3, x_146);
lean_ctor_set(x_45, 2, x_145);
lean_ctor_set(x_45, 1, x_144);
lean_ctor_set(x_45, 0, x_143);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_147);
x_153 = 0;
lean_ctor_set(x_44, 3, x_45);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_153);
return x_44;
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_45);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_147);
x_155 = 0;
lean_ctor_set(x_44, 3, x_154);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_155);
return x_44;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_ctor_get(x_127, 0);
x_157 = lean_ctor_get(x_127, 1);
x_158 = lean_ctor_get(x_127, 2);
x_159 = lean_ctor_get(x_127, 3);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_127);
x_160 = 1;
lean_inc(x_45);
x_161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_161, 0, x_35);
lean_ctor_set(x_161, 1, x_36);
lean_ctor_set(x_161, 2, x_37);
lean_ctor_set(x_161, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_162 = x_45;
} else {
 lean_dec_ref(x_45);
 x_162 = lean_box(0);
}
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_160);
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_157);
lean_ctor_set(x_163, 2, x_158);
lean_ctor_set(x_163, 3, x_159);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_160);
x_164 = 0;
lean_ctor_set(x_44, 3, x_163);
lean_ctor_set(x_44, 0, x_161);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_164);
return x_44;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_165 = lean_ctor_get(x_44, 1);
x_166 = lean_ctor_get(x_44, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_167 = lean_ctor_get(x_127, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_127, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_127, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_127, 3);
lean_inc(x_170);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_171 = x_127;
} else {
 lean_dec_ref(x_127);
 x_171 = lean_box(0);
}
x_172 = 1;
lean_inc(x_45);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_35);
lean_ctor_set(x_173, 1, x_36);
lean_ctor_set(x_173, 2, x_37);
lean_ctor_set(x_173, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_174 = x_45;
} else {
 lean_dec_ref(x_45);
 x_174 = lean_box(0);
}
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_168);
lean_ctor_set(x_175, 2, x_169);
lean_ctor_set(x_175, 3, x_170);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_172);
x_176 = 0;
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_165);
lean_ctor_set(x_177, 2, x_166);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_44);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_44, 3);
lean_dec(x_179);
x_180 = lean_ctor_get(x_44, 0);
lean_dec(x_180);
x_181 = !lean_is_exclusive(x_45);
if (x_181 == 0)
{
uint8_t x_182; uint8_t x_183; 
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_138);
x_182 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_184 = lean_ctor_get(x_45, 0);
x_185 = lean_ctor_get(x_45, 1);
x_186 = lean_ctor_get(x_45, 2);
x_187 = lean_ctor_get(x_45, 3);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_45);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_138);
x_189 = 0;
lean_ctor_set(x_44, 0, x_188);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_189);
x_190 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; 
x_191 = lean_ctor_get(x_44, 1);
x_192 = lean_ctor_get(x_44, 2);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_44);
x_193 = lean_ctor_get(x_45, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_45, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_45, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_45, 3);
lean_inc(x_196);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_197 = x_45;
} else {
 lean_dec_ref(x_45);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 4, 1);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_138);
x_199 = 0;
x_200 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_192);
lean_ctor_set(x_200, 3, x_127);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_199);
x_201 = 1;
lean_ctor_set(x_1, 3, x_200);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
}
}
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_37);
lean_dec(x_36);
x_202 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
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
x_370 = lean_string_dec_eq(x_2, x_366);
if (x_370 == 0)
{
uint8_t x_371; 
x_371 = l_Std_RBNode_isRed___rarg(x_368);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_372 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_368, x_2, x_3);
x_373 = 1;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_365);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_367);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_368, x_2, x_3);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_375, 3);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_380 = x_375;
} else {
 lean_dec_ref(x_375);
 x_380 = lean_box(0);
}
x_381 = 0;
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(1, 4, 1);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_377);
lean_ctor_set(x_382, 1, x_378);
lean_ctor_set(x_382, 2, x_379);
lean_ctor_set(x_382, 3, x_377);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_381);
x_383 = 1;
x_384 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_384, 0, x_365);
lean_ctor_set(x_384, 1, x_366);
lean_ctor_set(x_384, 2, x_367);
lean_ctor_set(x_384, 3, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
return x_384;
}
else
{
uint8_t x_385; 
x_385 = lean_ctor_get_uint8(x_377, sizeof(void*)*4);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_386 = lean_ctor_get(x_375, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_375, 2);
lean_inc(x_387);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_388 = x_375;
} else {
 lean_dec_ref(x_375);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_377, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_377, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_377, 3);
lean_inc(x_392);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_393 = x_377;
} else {
 lean_dec_ref(x_377);
 x_393 = lean_box(0);
}
x_394 = 1;
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_365);
lean_ctor_set(x_395, 1, x_366);
lean_ctor_set(x_395, 2, x_367);
lean_ctor_set(x_395, 3, x_376);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_388)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_388;
}
lean_ctor_set(x_396, 0, x_389);
lean_ctor_set(x_396, 1, x_390);
lean_ctor_set(x_396, 2, x_391);
lean_ctor_set(x_396, 3, x_392);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_394);
x_397 = 0;
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_386);
lean_ctor_set(x_398, 2, x_387);
lean_ctor_set(x_398, 3, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; 
x_399 = lean_ctor_get(x_375, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_375, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_401 = x_375;
} else {
 lean_dec_ref(x_375);
 x_401 = lean_box(0);
}
x_402 = 0;
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_376);
lean_ctor_set(x_403, 1, x_399);
lean_ctor_set(x_403, 2, x_400);
lean_ctor_set(x_403, 3, x_377);
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
x_404 = 1;
x_405 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_405, 0, x_365);
lean_ctor_set(x_405, 1, x_366);
lean_ctor_set(x_405, 2, x_367);
lean_ctor_set(x_405, 3, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
x_406 = lean_ctor_get_uint8(x_376, sizeof(void*)*4);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_407 = lean_ctor_get(x_375, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_375, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_375, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_410 = x_375;
} else {
 lean_dec_ref(x_375);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_376, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_376, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_376, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_376, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_415 = x_376;
} else {
 lean_dec_ref(x_376);
 x_415 = lean_box(0);
}
x_416 = 1;
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_415;
}
lean_ctor_set(x_417, 0, x_365);
lean_ctor_set(x_417, 1, x_366);
lean_ctor_set(x_417, 2, x_367);
lean_ctor_set(x_417, 3, x_411);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_416);
if (lean_is_scalar(x_410)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_410;
}
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_407);
lean_ctor_set(x_418, 2, x_408);
lean_ctor_set(x_418, 3, x_409);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_416);
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_412);
lean_ctor_set(x_420, 2, x_413);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
else
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_375, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_375, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_375, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_424 = x_375;
} else {
 lean_dec_ref(x_375);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_376);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_365);
lean_ctor_set(x_428, 1, x_366);
lean_ctor_set(x_428, 2, x_367);
lean_ctor_set(x_428, 3, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; 
x_430 = lean_ctor_get(x_375, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_375, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_432 = x_375;
} else {
 lean_dec_ref(x_375);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
lean_inc(x_376);
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_365);
lean_ctor_set(x_439, 1, x_366);
lean_ctor_set(x_439, 2, x_367);
lean_ctor_set(x_439, 3, x_376);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_440 = x_376;
} else {
 lean_dec_ref(x_376);
 x_440 = lean_box(0);
}
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_433);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_436);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_438);
x_442 = 0;
if (lean_is_scalar(x_432)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_432;
}
lean_ctor_set(x_443, 0, x_439);
lean_ctor_set(x_443, 1, x_430);
lean_ctor_set(x_443, 2, x_431);
lean_ctor_set(x_443, 3, x_441);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; 
x_444 = lean_ctor_get(x_375, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_375, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_446 = x_375;
} else {
 lean_dec_ref(x_375);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_376, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_376, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_376, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_376, 3);
lean_inc(x_450);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_451 = x_376;
} else {
 lean_dec_ref(x_376);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_447);
lean_ctor_set(x_452, 1, x_448);
lean_ctor_set(x_452, 2, x_449);
lean_ctor_set(x_452, 3, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_429);
x_453 = 0;
if (lean_is_scalar(x_446)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_446;
}
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_444);
lean_ctor_set(x_454, 2, x_445);
lean_ctor_set(x_454, 3, x_421);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
x_455 = 1;
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_365);
lean_ctor_set(x_456, 1, x_366);
lean_ctor_set(x_456, 2, x_367);
lean_ctor_set(x_456, 3, x_454);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
return x_456;
}
}
}
}
}
}
else
{
uint8_t x_457; lean_object* x_458; 
lean_dec(x_367);
lean_dec(x_366);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_2);
lean_ctor_set(x_458, 2, x_3);
lean_ctor_set(x_458, 3, x_368);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
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
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_updateFileWorkers(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_updateFileWorkers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_updateFileWorkers(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = lean_string_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1(x_7, x_1);
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
x_11 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1(x_9, x_1);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findFileWorker_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cannot find open document '", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findFileWorker_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_Watchdog_findFileWorker_x3f(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_IO_throwServerError___rarg(x_10, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findFileWorker_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker_x21(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_string_dec_eq(x_1, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_8);
x_13 = 0;
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_2);
x_14 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_8);
x_15 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_16 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_16;
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
x_27 = lean_string_dec_eq(x_1, x_23);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Std_RBNode_isBlack___rarg(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_25);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_25);
x_33 = l_Std_RBNode_balRight___rarg(x_22, x_23, x_24, x_32);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
x_34 = l_Std_RBNode_appendTrees___rarg(x_22, x_25);
return x_34;
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
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_eraseFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = l_System_Uri_fileUriToPath_x3f(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 8);
x_17 = l_Lean_searchModuleNameOfFileName(x_15, x_16, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_2, 9);
x_28 = lean_st_ref_take(x_27, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Server_References_removeWorkerRefs(x_29, x_26);
lean_dec(x_26);
x_32 = lean_st_ref_set(x_27, x_31, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_dec(x_9);
x_38 = l_System_Uri_fileUriToPath_x3f(x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_2, 8);
x_43 = l_Lean_searchModuleNameOfFileName(x_41, x_42, x_37);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_ctor_get(x_2, 9);
x_52 = lean_st_ref_take(x_51, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Server_References_removeWorkerRefs(x_53, x_50);
lean_dec(x_50);
x_56 = lean_st_ref_set(x_51, x_55, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_eraseFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_log(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
x_5 = l_IO_FS_Stream_putStrLn(x_4, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 0);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoUpdate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_System_Uri_fileUriToPath_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_3, 8);
x_13 = l_Lean_searchModuleNameOfFileName(x_11, x_12, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_3, 9);
x_24 = lean_st_ref_take(x_23, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_Server_References_updateWorkerRefs(x_25, x_22, x_27, x_28);
x_30 = lean_st_ref_set(x_23, x_29, x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoUpdate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleIleanInfoUpdate(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_System_Uri_fileUriToPath_x3f(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_3, 8);
x_13 = l_Lean_searchModuleNameOfFileName(x_11, x_12, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_3, 9);
x_24 = lean_st_ref_take(x_23, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_Server_References_finalizeWorkerRefs(x_25, x_22, x_27, x_28);
x_30 = lean_st_ref_set(x_23, x_29, x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleIleanInfoFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleIleanInfoFinal(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(x_1, x_2, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Server process for ", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" crashed, ", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("likely due to a stack overflow or a bug", 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("see stderr for exception", 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("The file worker has been terminated. Either the header has changed,", 67);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" or the file was closed, or the server is shutting down.", 56);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__6;
x_2 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9() {
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
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/ileanInfoUpdate", 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/ileanInfoFinal", 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; lean_object* x_89; lean_object* x_90; 
lean_inc(x_1);
x_89 = l_Lean_Server_Watchdog_FileWorker_stdout(x_1);
x_90 = l_IO_FS_Stream_readLspMessage(x_89, x_4);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
switch (lean_obj_tag(x_91)) {
case 0:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_2);
x_93 = l_IO_FS_Stream_writeLspMessage(x_2, x_91, x_92);
lean_dec(x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_5 = x_97;
x_6 = x_95;
goto block_10;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_11 = x_98;
x_12 = x_99;
goto block_88;
}
}
case 1:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_ctor_get(x_91, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_91, 1);
lean_inc(x_102);
x_103 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__10;
x_104 = lean_string_dec_eq(x_101, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__11;
x_106 = lean_string_dec_eq(x_101, x_105);
lean_dec(x_101);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_102);
lean_inc(x_2);
x_107 = l_IO_FS_Stream_writeLspMessage(x_2, x_91, x_100);
lean_dec(x_91);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_5 = x_111;
x_6 = x_109;
goto block_10;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_11 = x_112;
x_12 = x_113;
goto block_88;
}
}
else
{
lean_dec(x_91);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_114; 
x_114 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
x_5 = x_114;
x_6 = x_100;
goto block_10;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_102, 0);
lean_inc(x_115);
lean_dec(x_102);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_827_(x_117);
lean_dec(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_dec(x_118);
x_119 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
x_5 = x_119;
x_6 = x_100;
goto block_10;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_1);
x_121 = l_Lean_Server_Watchdog_handleIleanInfoFinal(x_1, x_120, x_3, x_100);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
x_5 = x_125;
x_6 = x_123;
goto block_10;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_115, 0);
lean_inc(x_126);
lean_dec(x_115);
x_127 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_827_(x_127);
lean_dec(x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec(x_128);
x_129 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
x_5 = x_129;
x_6 = x_100;
goto block_10;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_1);
x_131 = l_Lean_Server_Watchdog_handleIleanInfoFinal(x_1, x_130, x_3, x_100);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_5 = x_135;
x_6 = x_133;
goto block_10;
}
}
}
}
}
else
{
lean_dec(x_101);
lean_dec(x_91);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_136; 
x_136 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
x_5 = x_136;
x_6 = x_100;
goto block_10;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_102, 0);
lean_inc(x_137);
lean_dec(x_102);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_827_(x_139);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_dec(x_140);
x_141 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
x_5 = x_141;
x_6 = x_100;
goto block_10;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_1);
x_143 = l_Lean_Server_Watchdog_handleIleanInfoUpdate(x_1, x_142, x_3, x_100);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_5 = x_147;
x_6 = x_145;
goto block_10;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_137, 0);
lean_inc(x_148);
lean_dec(x_137);
x_149 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_fromJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_827_(x_149);
lean_dec(x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_dec(x_150);
x_151 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12;
x_5 = x_151;
x_6 = x_100;
goto block_10;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_1);
x_153 = l_Lean_Server_Watchdog_handleIleanInfoUpdate(x_1, x_152, x_3, x_100);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_156);
x_5 = x_157;
x_6 = x_155;
goto block_10;
}
}
}
}
}
default: 
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_90, 1);
lean_inc(x_158);
lean_dec(x_90);
x_159 = lean_ctor_get(x_91, 0);
lean_inc(x_159);
x_160 = l_Lean_Server_Watchdog_FileWorker_erasePendingRequest(x_1, x_159, x_158);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
lean_inc(x_2);
x_162 = l_IO_FS_Stream_writeLspMessage(x_2, x_91, x_161);
lean_dec(x_91);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_5 = x_166;
x_6 = x_164;
goto block_10;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_dec(x_162);
x_11 = x_167;
x_12 = x_168;
goto block_88;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_90, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_90, 1);
lean_inc(x_170);
lean_dec(x_90);
x_171 = lean_ctor_get(x_1, 1);
lean_inc(x_171);
x_172 = l_Lean_Server_Watchdog_workerCfg;
x_173 = lean_io_process_child_wait(x_172, x_171, x_170);
lean_dec(x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint32_t x_176; uint32_t x_177; uint8_t x_178; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = 0;
x_177 = lean_unbox_uint32(x_174);
x_178 = lean_uint32_dec_eq(x_177, x_176);
if (x_178 == 0)
{
uint32_t x_179; uint32_t x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_179 = 1;
x_180 = lean_unbox_uint32(x_174);
lean_dec(x_174);
x_181 = lean_uint32_dec_eq(x_180, x_179);
x_182 = lean_ctor_get(x_1, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
x_186 = lean_string_append(x_185, x_184);
lean_dec(x_184);
x_187 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
x_188 = lean_string_append(x_186, x_187);
if (x_181 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; 
x_189 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
x_190 = lean_string_append(x_188, x_189);
x_191 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
x_192 = lean_string_append(x_190, x_191);
x_193 = 11;
lean_inc(x_2);
x_194 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_193, x_192, x_175);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_unsigned_to_nat(0u);
x_197 = 1;
lean_inc(x_2);
x_198 = l_Lean_Server_publishProgressAtPos(x_183, x_196, x_2, x_197, x_195);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_200, 0, x_169);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_5 = x_202;
x_6 = x_199;
goto block_10;
}
else
{
uint8_t x_203; 
lean_dec(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_198);
if (x_203 == 0)
{
return x_198;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_198, 0);
x_205 = lean_ctor_get(x_198, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_198);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_183);
lean_dec(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_194);
if (x_207 == 0)
{
return x_194;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_194, 0);
x_209 = lean_ctor_get(x_194, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_194);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
x_211 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
x_212 = lean_string_append(x_188, x_211);
x_213 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
x_214 = lean_string_append(x_212, x_213);
x_215 = 10;
lean_inc(x_2);
x_216 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_215, x_214, x_175);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_unsigned_to_nat(0u);
x_219 = 1;
lean_inc(x_2);
x_220 = l_Lean_Server_publishProgressAtPos(x_183, x_218, x_2, x_219, x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_222, 0, x_169);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_5 = x_224;
x_6 = x_221;
goto block_10;
}
else
{
uint8_t x_225; 
lean_dec(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_220);
if (x_225 == 0)
{
return x_220;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_220, 0);
x_227 = lean_ctor_get(x_220, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_220);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_183);
lean_dec(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_216);
if (x_229 == 0)
{
return x_216;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_216, 0);
x_231 = lean_ctor_get(x_216, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_216);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
else
{
uint8_t x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_174);
lean_dec(x_169);
x_233 = 7;
x_234 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8;
lean_inc(x_2);
x_235 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_233, x_234, x_175);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9;
x_5 = x_237;
x_6 = x_236;
goto block_10;
}
else
{
uint8_t x_238; 
lean_dec(x_2);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_235);
if (x_238 == 0)
{
return x_235;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_235, 0);
x_240 = lean_ctor_get(x_235, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_235);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_169);
lean_dec(x_2);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_173);
if (x_242 == 0)
{
return x_173;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_173, 0);
x_244 = lean_ctor_get(x_173, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_173);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
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
block_88:
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
x_20 = lean_uint32_dec_eq(x_19, x_18);
if (x_20 == 0)
{
uint32_t x_21; uint32_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = 1;
x_22 = lean_unbox_uint32(x_16);
lean_dec(x_16);
x_23 = lean_uint32_dec_eq(x_22, x_21);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
x_30 = lean_string_append(x_28, x_29);
if (x_23 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_31 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
x_34 = lean_string_append(x_32, x_33);
x_35 = 11;
lean_inc(x_2);
x_36 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_35, x_34, x_17);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = 1;
lean_inc(x_2);
x_40 = l_Lean_Server_publishProgressAtPos(x_25, x_38, x_2, x_39, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_11);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_5 = x_44;
x_6 = x_41;
goto block_10;
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_53 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
x_54 = lean_string_append(x_30, x_53);
x_55 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
x_56 = lean_string_append(x_54, x_55);
x_57 = 10;
lean_inc(x_2);
x_58 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_57, x_56, x_17);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = 1;
lean_inc(x_2);
x_62 = l_Lean_Server_publishProgressAtPos(x_25, x_60, x_2, x_61, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_11);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_5 = x_66;
x_6 = x_63;
goto block_10;
}
else
{
uint8_t x_67; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_58);
if (x_71 == 0)
{
return x_58;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_58, 0);
x_73 = lean_ctor_get(x_58, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_58);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_16);
lean_dec(x_11);
x_75 = 7;
x_76 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__8;
lean_inc(x_2);
x_77 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_75, x_76, x_17);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9;
x_5 = x_79;
x_6 = x_78;
goto block_10;
}
else
{
uint8_t x_80; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_15);
if (x_84 == 0)
{
return x_15;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_15, 0);
x_86 = lean_ctor_get(x_15, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_15);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Task_Priority_dedicated;
x_8 = lean_io_as_task(x_6, x_7, x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_12 = l_Task_Priority_default;
x_13 = lean_task_map(x_11, x_10, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1;
x_17 = l_Task_Priority_default;
x_18 = lean_task_map(x_16, x_14, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected structured object, got '", 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_400_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_IO_FS_Stream_writeLspMessage(x_1, x_10, x_3);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_117_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_1, x_9, x_3);
lean_dec(x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("--worker", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
x_2 = l_Lean_Server_Watchdog_startFileWorker___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_JsonNumber_fromNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_startFileWorker___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initialize", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/didOpen", 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_startFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
lean_inc(x_1);
x_7 = l_Lean_Server_publishProgressAtPos(x_1, x_5, x_4, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_12, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
x_18 = l_List_redLength___rarg(x_17);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_dec(x_18);
x_20 = l_List_toArrayAux___rarg(x_17, x_19);
x_21 = l_Lean_Server_Watchdog_startFileWorker___closed__3;
x_22 = l_Array_append___rarg(x_21, x_20);
x_23 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
lean_inc(x_9);
x_24 = lean_array_push(x_23, x_9);
x_25 = l_Array_append___rarg(x_22, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Server_Watchdog_workerCfg;
x_28 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_io_process_spawn(x_29, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_st_mk_ref(x_33, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_mk_ref(x_26, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_14);
x_41 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_42 = lean_box(1);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_31);
lean_inc(x_40);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_38);
lean_inc(x_2);
x_44 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(x_43, x_2, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_31);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_35);
lean_ctor_set(x_47, 5, x_38);
lean_inc(x_47);
x_48 = l_Lean_Server_Watchdog_FileWorker_stdin(x_47);
x_49 = lean_ctor_get(x_2, 5);
lean_inc(x_49);
x_50 = l_Lean_Server_Watchdog_startFileWorker___closed__7;
x_51 = l_Lean_Server_Watchdog_startFileWorker___closed__8;
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_49);
lean_inc(x_48);
x_53 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__1(x_48, x_52, x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Server_Watchdog_startFileWorker___closed__9;
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_9);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_10);
lean_ctor_set(x_56, 3, x_12);
x_57 = l_Lean_Server_Watchdog_startFileWorker___closed__10;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__3(x_48, x_58, x_54);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Server_Watchdog_updateFileWorkers(x_47, x_2, x_60);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
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
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
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
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_30);
if (x_70 == 0)
{
return x_30;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_30, 0);
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_30);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_13);
if (x_74 == 0)
{
return x_13;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_13, 0);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_13);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_7);
if (x_78 == 0)
{
return x_7;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_7, 0);
x_80 = lean_ctor_get(x_7, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_7);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker_x21(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Server_Watchdog_FileWorker_stdin(x_5);
x_8 = l_Lean_Server_Watchdog_terminateFileWorker___closed__2;
x_9 = l_IO_FS_Stream_writeLspMessage(x_7, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_terminateFileWorker___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_terminateFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_terminateFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleCrash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_findFileWorker_x21(x_1, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleCrash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleCrash(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
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
x_15 = lean_usize_add(x_4, x_14);
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
x_20 = lean_usize_add(x_4, x_19);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
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
x_13 = l_Lean_Server_Watchdog_findFileWorker_x21(x_1, x_5, x_12);
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
x_19 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_dec(x_5);
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_6);
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
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_21 = l_Lean_Server_Watchdog_handleCrash(x_3, x_20, x_7, x_19);
lean_dec(x_7);
lean_dec(x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
lean_inc(x_5);
x_23 = lean_array_push(x_22, x_5);
x_24 = l_IO_FS_Stream_writeLspMessage(x_17, x_5, x_8);
lean_dec(x_5);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_3);
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
lean_dec(x_3);
return x_26;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot send message to unknown document '", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("':\n", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("2.0", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("jsonrpc", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__6;
x_2 = l_Lean_Server_Watchdog_tryWriteMessage___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("method", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("params", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("message", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("data", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__17;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__18;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__21;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__22;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__25;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__29;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__30;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__33;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__34;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__35;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__37;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__38;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__39;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__41;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__42;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__43;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__45;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__46;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__47;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__49;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__50;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__51;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__53;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__54;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__55;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__57;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__58;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__59;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__61;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__62;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___closed__63;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Server_Watchdog_findFileWorker_x3f(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___closed__1;
x_12 = lean_string_append(x_11, x_1);
lean_dec(x_1);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage___closed__2;
x_14 = lean_string_append(x_12, x_13);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
x_41 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_40, x_34);
lean_dec(x_34);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
x_47 = l_List_appendTR___rarg(x_46, x_41);
x_48 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Json_mkObj(x_49);
x_15 = x_50;
goto block_31;
}
case 1:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
lean_dec(x_32);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_39);
x_56 = l_List_appendTR___rarg(x_55, x_41);
x_57 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Json_mkObj(x_58);
x_15 = x_59;
goto block_31;
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_39);
x_62 = l_List_appendTR___rarg(x_61, x_41);
x_63 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Json_mkObj(x_64);
x_15 = x_65;
goto block_31;
}
}
}
case 1:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
lean_dec(x_2);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_66);
x_69 = l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
x_72 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_71, x_67);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Json_mkObj(x_75);
x_15 = x_76;
goto block_31;
}
case 2:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
lean_dec(x_2);
x_79 = l_Lean_Server_Watchdog_tryWriteMessage___closed__12;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
switch (lean_obj_tag(x_77)) {
case 0:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
x_88 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_Json_mkObj(x_89);
x_15 = x_90;
goto block_31;
}
case 1:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_77, 0);
lean_inc(x_91);
lean_dec(x_77);
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_82);
x_96 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Json_mkObj(x_97);
x_15 = x_98;
goto block_31;
}
default: 
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_82);
x_101 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Json_mkObj(x_102);
x_15 = x_103;
goto block_31;
}
}
}
default: 
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_104 = lean_ctor_get(x_2, 0);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_106 = lean_ctor_get(x_2, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
lean_dec(x_2);
x_108 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_108, 0, x_106);
x_109 = l_Lean_Server_Watchdog_tryWriteMessage___closed__13;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Server_Watchdog_tryWriteMessage___closed__14;
x_114 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_113, x_107);
lean_dec(x_107);
switch (lean_obj_tag(x_104)) {
case 0:
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_104, 0);
lean_inc(x_145);
lean_dec(x_104);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_115 = x_146;
goto block_144;
}
case 1:
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_104, 0);
lean_inc(x_147);
lean_dec(x_104);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_115 = x_148;
goto block_144;
}
default: 
{
lean_object* x_149; 
x_149 = lean_box(0);
x_115 = x_149;
goto block_144;
}
}
block_144:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
switch (x_105) {
case 0:
{
lean_object* x_132; 
x_132 = l_Lean_Server_Watchdog_tryWriteMessage___closed__20;
x_118 = x_132;
goto block_131;
}
case 1:
{
lean_object* x_133; 
x_133 = l_Lean_Server_Watchdog_tryWriteMessage___closed__24;
x_118 = x_133;
goto block_131;
}
case 2:
{
lean_object* x_134; 
x_134 = l_Lean_Server_Watchdog_tryWriteMessage___closed__28;
x_118 = x_134;
goto block_131;
}
case 3:
{
lean_object* x_135; 
x_135 = l_Lean_Server_Watchdog_tryWriteMessage___closed__32;
x_118 = x_135;
goto block_131;
}
case 4:
{
lean_object* x_136; 
x_136 = l_Lean_Server_Watchdog_tryWriteMessage___closed__36;
x_118 = x_136;
goto block_131;
}
case 5:
{
lean_object* x_137; 
x_137 = l_Lean_Server_Watchdog_tryWriteMessage___closed__40;
x_118 = x_137;
goto block_131;
}
case 6:
{
lean_object* x_138; 
x_138 = l_Lean_Server_Watchdog_tryWriteMessage___closed__44;
x_118 = x_138;
goto block_131;
}
case 7:
{
lean_object* x_139; 
x_139 = l_Lean_Server_Watchdog_tryWriteMessage___closed__48;
x_118 = x_139;
goto block_131;
}
case 8:
{
lean_object* x_140; 
x_140 = l_Lean_Server_Watchdog_tryWriteMessage___closed__52;
x_118 = x_140;
goto block_131;
}
case 9:
{
lean_object* x_141; 
x_141 = l_Lean_Server_Watchdog_tryWriteMessage___closed__56;
x_118 = x_141;
goto block_131;
}
case 10:
{
lean_object* x_142; 
x_142 = l_Lean_Server_Watchdog_tryWriteMessage___closed__60;
x_118 = x_142;
goto block_131;
}
default: 
{
lean_object* x_143; 
x_143 = l_Lean_Server_Watchdog_tryWriteMessage___closed__64;
x_118 = x_143;
goto block_131;
}
}
block_131:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_119 = l_Lean_Server_Watchdog_tryWriteMessage___closed__15;
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_112);
x_122 = l_List_appendTR___rarg(x_121, x_114);
x_123 = l_Lean_Json_mkObj(x_122);
x_124 = l_Lean_Server_Watchdog_tryWriteMessage___closed__16;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_111);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Json_mkObj(x_129);
x_15 = x_130;
goto block_31;
}
}
}
}
block_31:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Json_compress(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_IO_FS_Stream_putStrLn(x_10, x_19, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_150 = lean_ctor_get(x_7, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_151 = x_7;
} else {
 lean_dec_ref(x_7);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_8, 0);
lean_inc(x_152);
lean_dec(x_8);
x_160 = lean_ctor_get(x_152, 5);
lean_inc(x_160);
x_161 = lean_st_ref_take(x_160, x_150);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_box(0);
x_165 = lean_st_ref_set(x_160, x_164, x_163);
lean_dec(x_160);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = 0;
x_153 = x_167;
x_154 = x_166;
goto block_159;
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_162);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_162, 0);
x_170 = lean_ctor_get(x_161, 1);
lean_inc(x_170);
lean_dec(x_161);
x_171 = !lean_is_exclusive(x_169);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_169, 3);
lean_inc(x_2);
x_173 = lean_array_push(x_172, x_2);
lean_ctor_set(x_169, 3, x_173);
x_174 = lean_st_ref_set(x_160, x_162, x_170);
lean_dec(x_160);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = 1;
x_153 = x_176;
x_154 = x_175;
goto block_159;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_177 = lean_ctor_get(x_169, 0);
x_178 = lean_ctor_get(x_169, 1);
x_179 = lean_ctor_get(x_169, 2);
x_180 = lean_ctor_get(x_169, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_169);
lean_inc(x_2);
x_181 = lean_array_push(x_180, x_2);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_177);
lean_ctor_set(x_182, 1, x_178);
lean_ctor_set(x_182, 2, x_179);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set(x_162, 0, x_182);
x_183 = lean_st_ref_set(x_160, x_162, x_170);
lean_dec(x_160);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = 1;
x_153 = x_185;
x_154 = x_184;
goto block_159;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_186 = lean_ctor_get(x_162, 0);
lean_inc(x_186);
lean_dec(x_162);
x_187 = lean_ctor_get(x_161, 1);
lean_inc(x_187);
lean_dec(x_161);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 x_192 = x_186;
} else {
 lean_dec_ref(x_186);
 x_192 = lean_box(0);
}
lean_inc(x_2);
x_193 = lean_array_push(x_191, x_2);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 4, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_188);
lean_ctor_set(x_194, 1, x_189);
lean_ctor_set(x_194, 2, x_190);
lean_ctor_set(x_194, 3, x_193);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = lean_st_ref_set(x_160, x_195, x_187);
lean_dec(x_160);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = 1;
x_153 = x_198;
x_154 = x_197;
goto block_159;
}
}
block_159:
{
if (x_153 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_151);
x_155 = lean_box(0);
x_156 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(x_152, x_4, x_1, x_3, x_2, x_155, x_5, x_154);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_152);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_151;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___lambda__3(x_1, x_9, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_tryWriteMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_findDefinitions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_12 = l_Lean_Server_References_definitionOf_x3f(x_2, x_11, x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_8 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_array_push(x_6, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
x_5 = x_22;
x_6 = x_20;
x_8 = x_18;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findDefinitions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findDefinitions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_findDefinitions___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findDefinitions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Server_Watchdog_findDefinitions___closed__1;
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_8 = lean_box(0);
x_9 = lean_apply_4(x_4, x_7, x_8, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_2, 8);
lean_inc(x_11);
x_12 = l_Lean_searchModuleNameOfFileName(x_10, x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_16 = lean_box(0);
x_17 = lean_apply_4(x_4, x_15, x_16, x_2, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_2, 9);
lean_inc(x_20);
x_21 = lean_st_ref_get(x_20, x_18);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_22);
x_25 = l_Lean_Server_References_findAt(x_22, x_19, x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_30 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_findDefinitions___spec__1(x_11, x_22, x_25, x_27, x_28, x_29, x_2, x_23);
lean_dec(x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_apply_4(x_4, x_31, x_33, x_2, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_findDefinitions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_findDefinitions___spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findDefinitions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_findDefinitions___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleReference___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_7, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_5, x_7);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_4);
x_16 = l_Lean_Server_References_referringTo(x_4, x_3, x_13, x_2, x_15, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_append___rarg(x_8, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_7 = x_21;
x_8 = x_19;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleReference(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_2, 8);
lean_inc(x_10);
x_11 = l_Lean_searchModuleNameOfFileName(x_9, x_10, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_2, 9);
lean_inc(x_21);
x_22 = lean_st_ref_get(x_21, x_19);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
lean_inc(x_20);
lean_inc(x_23);
x_26 = l_Lean_Server_References_findAt(x_23, x_20, x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_31 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleReference___spec__1(x_1, x_10, x_20, x_23, x_26, x_28, x_29, x_30, x_2, x_24);
lean_dec(x_2);
lean_dec(x_26);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleReference___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleReference___spec__1(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; double x_7; double x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unbox_float(x_6);
lean_dec(x_6);
x_8 = lean_unbox_float(x_5);
lean_dec(x_5);
x_9 = lean_float_decLt(x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_4);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; double x_63; double x_64; uint8_t x_65; 
x_15 = lean_nat_add(x_3, x_4);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
lean_inc(x_1);
x_57 = lean_array_get(x_1, x_2, x_17);
lean_inc(x_1);
x_58 = lean_array_get(x_1, x_2, x_3);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox_float(x_62);
lean_dec(x_62);
x_64 = lean_unbox_float(x_61);
lean_dec(x_61);
x_65 = lean_float_decLt(x_63, x_64);
if (x_65 == 0)
{
x_18 = x_2;
goto block_56;
}
else
{
lean_object* x_66; 
x_66 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_66;
goto block_56;
}
block_56:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; double x_25; double x_26; uint8_t x_27; 
lean_inc(x_1);
x_19 = lean_array_get(x_1, x_18, x_4);
lean_inc(x_1);
x_20 = lean_array_get(x_1, x_18, x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unbox_float(x_24);
lean_dec(x_24);
x_26 = lean_unbox_float(x_23);
x_27 = lean_float_decLt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; double x_31; double x_32; uint8_t x_33; 
lean_inc(x_1);
x_28 = lean_array_get(x_1, x_18, x_17);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unbox_float(x_23);
lean_dec(x_23);
x_32 = lean_unbox_float(x_30);
lean_dec(x_30);
x_33 = lean_float_decLt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
x_34 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_35 = l_Array_qpartition_loop___rarg(x_1, x_34, x_4, x_19, x_18, x_3, x_3);
x_5 = x_35;
goto block_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_19);
x_36 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_37 = lean_array_get(x_1, x_36, x_4);
x_38 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_39 = l_Array_qpartition_loop___rarg(x_1, x_38, x_4, x_37, x_36, x_3, x_3);
x_5 = x_39;
goto block_13;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; double x_47; double x_48; uint8_t x_49; 
lean_dec(x_23);
lean_dec(x_19);
x_40 = lean_array_swap(x_18, x_3, x_4);
lean_inc(x_1);
x_41 = lean_array_get(x_1, x_40, x_17);
lean_inc(x_1);
x_42 = lean_array_get(x_1, x_40, x_4);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox_float(x_46);
lean_dec(x_46);
x_48 = lean_unbox_float(x_45);
lean_dec(x_45);
x_49 = lean_float_decLt(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_17);
x_50 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_51 = l_Array_qpartition_loop___rarg(x_1, x_50, x_4, x_42, x_40, x_3, x_3);
x_5 = x_51;
goto block_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_42);
x_52 = lean_array_swap(x_40, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_53 = lean_array_get(x_1, x_52, x_4);
x_54 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_55 = l_Array_qpartition_loop___rarg(x_1, x_54, x_4, x_53, x_52, x_3, x_3);
x_5 = x_55;
goto block_13;
}
}
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_9 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1(x_1, x_7, x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = 13;
x_15 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_16 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_14);
x_17 = lean_array_uset(x_7, x_2, x_16);
x_2 = x_9;
x_3 = x_17;
goto _start;
}
}
}
static double _init_l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_private_to_user_name(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; double x_6; lean_object* x_7; 
x_4 = 1;
x_5 = l_Lean_Name_toString(x_2, x_4);
x_6 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1___closed__1;
lean_inc(x_5);
x_7 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; double x_18; lean_object* x_19; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = 1;
x_17 = l_Lean_Name_toString(x_15, x_16);
x_18 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1___closed__1;
lean_inc(x_17);
x_19 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_instInhabitedString;
x_2 = l_instInhabitedFloat;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__1;
x_2 = l_Lean_Lsp_instInhabitedLocation;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 9);
lean_inc(x_5);
x_6 = lean_st_ref_get(x_5, x_4);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_3, 8);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = l_Lean_Server_References_definitionsMatching___rarg(x_7, x_9, x_10, x_11, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1(x_18, x_14, x_19, x_17);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(100u);
x_22 = l_Array_extract___rarg(x_20, x_19, x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2(x_24, x_25, x_22);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_array_get_size(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_32 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2;
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1(x_32, x_27, x_33, x_31);
lean_dec(x_31);
x_35 = lean_unsigned_to_nat(100u);
x_36 = l_Array_extract___rarg(x_34, x_33, x_35);
x_37 = lean_array_get_size(x_36);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
x_40 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2(x_38, x_39, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
return x_41;
}
}
else
{
uint8_t x_42; 
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_String_isEmpty(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2(x_1, x_5, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_431_(x_1);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
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
lean_inc(x_1);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage(x_1, x_10, x_11, x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
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
lean_inc(x_1);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage(x_1, x_10, x_11, x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
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
lean_dec(x_1);
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
x_1 = lean_mk_string_from_bytes("textDocument/didChange", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Server_foldDocumentChanges(x_2, x_19);
lean_inc(x_20);
lean_inc(x_3);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_22, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_18);
x_26 = l_Lean_Syntax_structEq(x_24, x_18);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_1);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = l_Lean_Server_Watchdog_terminateFileWorker(x_3, x_14, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Server_Watchdog_startFileWorker(x_21, x_14, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_14);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
lean_ctor_set(x_1, 0, x_21);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_5);
lean_ctor_set(x_34, 2, x_6);
lean_ctor_set(x_34, 3, x_7);
lean_ctor_set(x_34, 4, x_8);
lean_ctor_set(x_34, 5, x_9);
x_35 = l_Lean_Server_Watchdog_updateFileWorkers(x_34, x_14, x_25);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(x_10);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = 1;
lean_inc(x_14);
lean_inc(x_3);
x_43 = l_Lean_Server_Watchdog_tryWriteMessage(x_3, x_41, x_42, x_42, x_14, x_36);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_12, 3);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = 0;
x_49 = lean_box(0);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3(x_3, x_45, x_47, x_48, x_49, x_14, x_44);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
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
else
{
uint8_t x_59; 
lean_dec(x_14);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
return x_43;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_43);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_21);
lean_free_object(x_1);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_23);
if (x_63 == 0)
{
return x_23;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_23, 0);
x_65 = lean_ctor_get(x_23, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_23);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_1);
x_69 = lean_ctor_get(x_67, 2);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Server_foldDocumentChanges(x_2, x_69);
lean_inc(x_70);
lean_inc(x_3);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_4);
lean_ctor_set(x_71, 2, x_70);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_72, x_15);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_68);
x_76 = l_Lean_Syntax_structEq(x_74, x_68);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_68);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = l_Lean_Server_Watchdog_terminateFileWorker(x_3, x_14, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Server_Watchdog_startFileWorker(x_71, x_14, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_71);
lean_dec(x_14);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_68);
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_5);
lean_ctor_set(x_85, 2, x_6);
lean_ctor_set(x_85, 3, x_7);
lean_ctor_set(x_85, 4, x_8);
lean_ctor_set(x_85, 5, x_9);
x_86 = l_Lean_Server_Watchdog_updateFileWorkers(x_85, x_14, x_75);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleEdits___spec__1(x_10);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = 1;
lean_inc(x_14);
lean_inc(x_3);
x_94 = l_Lean_Server_Watchdog_tryWriteMessage(x_3, x_92, x_93, x_93, x_14, x_87);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_12, 3);
x_97 = lean_array_get_size(x_96);
x_98 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_99 = 0;
x_100 = lean_box(0);
x_101 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3(x_3, x_96, x_98, x_99, x_100, x_14, x_95);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_107 = x_101;
} else {
 lean_dec_ref(x_101);
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
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_14);
lean_dec(x_3);
x_109 = lean_ctor_get(x_94, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_94, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_111 = x_94;
} else {
 lean_dec_ref(x_94);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_113 = lean_ctor_get(x_73, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_73, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_115 = x_73;
} else {
 lean_dec_ref(x_73);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = l_Array_isEmpty___rarg(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Server_Watchdog_handleEdits___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17, x_14, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Internal error: empty grouped edits reference", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected version number", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleEdits___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got outdated version number", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_33 = l_Lean_Server_Watchdog_handleEdits___lambda__2(x_4, x_28, x_26, x_27, x_5, x_6, x_7, x_8, x_9, x_19, x_13, x_18, x_32, x_2, x_25);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleEdits___spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Server_Watchdog_handleEdits___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleEdits___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Server_Watchdog_handleEdits___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidClose(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_terminateFileWorker(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidClose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_handleDidClose(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_string_dec_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__2(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_18 = lean_array_uget(x_3, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_System_Uri_fileUriToPath_x3f(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_9 = x_21;
x_10 = x_8;
goto block_15;
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
switch (x_22) {
case 0:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_9 = x_25;
x_10 = x_8;
goto block_15;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Server_Ilean_load(x_23, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_1, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Server_References_addIlean(x_30, x_23, x_27);
x_33 = lean_st_ref_set(x_1, x_32, x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_9 = x_35;
x_10 = x_34;
goto block_15;
}
else
{
uint8_t x_36; 
lean_dec(x_23);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
case 1:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1(x_2, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_9 = x_42;
x_10 = x_8;
goto block_15;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Server_Ilean_load(x_40, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_st_ref_take(x_1, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_40);
x_49 = l_Lean_Server_References_removeIlean(x_47, x_40);
x_50 = l_Lean_Server_References_addIlean(x_49, x_40, x_44);
x_51 = lean_st_ref_set(x_1, x_50, x_48);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_9 = x_53;
x_10 = x_52;
goto block_15;
}
else
{
uint8_t x_54; 
lean_dec(x_40);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_20, 0);
lean_inc(x_58);
lean_dec(x_20);
x_59 = lean_st_ref_take(x_1, x_8);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Server_References_removeIlean(x_60, x_58);
x_63 = lean_st_ref_set(x_1, x_62, x_61);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_9 = x_65;
x_10 = x_64;
goto block_15;
}
}
}
}
block_15:
{
lean_object* x_11; size_t x_12; size_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_6 = x_11;
x_8 = x_10;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ilean", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidChangeWatchedFiles(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 9);
x_5 = l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1;
x_6 = lean_st_ref_get(x_5, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2;
x_10 = l_Lean_SearchPath_findAllWithExt(x_7, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_1);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = lean_box(0);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3(x_4, x_11, x_1, x_14, x_15, x_16, x_2, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_handleDidChangeWatchedFiles(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_2);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_2, x_5);
switch (x_8) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
lean_dec(x_6);
lean_dec(x_4);
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_83_(x_1);
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
x_1 = lean_mk_string_from_bytes("$/cancelRequest", 15);
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_dec(x_2);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_10, 4);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_st_ref_get(x_19, x_18);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(x_21, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_9);
x_24 = lean_box(0);
x_2 = x_11;
x_3 = x_24;
x_5 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_23, 0, x_29);
x_30 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
x_32 = 0;
lean_inc(x_4);
x_33 = l_Lean_Server_Watchdog_tryWriteMessage(x_9, x_31, x_32, x_32, x_4, x_22);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_2 = x_11;
x_3 = x_35;
x_5 = x_34;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_23);
x_41 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = 0;
lean_inc(x_4);
x_47 = l_Lean_Server_Watchdog_tryWriteMessage(x_9, x_45, x_46, x_46, x_4, x_22);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_2 = x_11;
x_3 = x_49;
x_5 = x_48;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_53 = x_47;
} else {
 lean_dec_ref(x_47);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleCancelRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = 0;
x_13 = l_Lean_Server_Watchdog_tryWriteMessage(x_7, x_10, x_11, x_12, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = 1;
x_18 = 0;
x_19 = l_Lean_Server_Watchdog_tryWriteMessage(x_7, x_16, x_17, x_18, x_5, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_forwardNotification___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got param with wrong structure: ", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_2);
x_8 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_parseParams___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_parseParams___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__1(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
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
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(80u);
x_9 = l_Lean_Json_pretty(x_1, x_8);
x_10 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_20);
lean_inc(x_2);
x_23 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_inc(x_2);
x_37 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_2, x_34);
switch (x_37) {
case 0:
{
uint8_t x_38; 
x_38 = l_Std_RBNode_isRed___rarg(x_33);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_33, x_2, x_3);
x_40 = 1;
lean_ctor_set(x_1, 0, x_39);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_33, x_2, x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_41, 3);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = 0;
lean_ctor_set(x_41, 0, x_43);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_47);
x_48 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = 0;
x_52 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = 1;
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
}
else
{
uint8_t x_54; 
x_54 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 2);
x_58 = lean_ctor_get(x_41, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_41, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_43);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_43, 0);
x_62 = lean_ctor_get(x_43, 1);
x_63 = lean_ctor_get(x_43, 2);
x_64 = lean_ctor_get(x_43, 3);
x_65 = 1;
lean_ctor_set(x_43, 3, x_61);
lean_ctor_set(x_43, 2, x_57);
lean_ctor_set(x_43, 1, x_56);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_65);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_64);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_65);
x_66 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_63);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_43, 0);
x_68 = lean_ctor_get(x_43, 1);
x_69 = lean_ctor_get(x_43, 2);
x_70 = lean_ctor_get(x_43, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_43);
x_71 = 1;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_42);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_70);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_71);
x_73 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_72);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_74 = lean_ctor_get(x_41, 1);
x_75 = lean_ctor_get(x_41, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_41);
x_76 = lean_ctor_get(x_43, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_43, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_80 = x_43;
} else {
 lean_dec_ref(x_43);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_42);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_34);
lean_ctor_set(x_83, 2, x_35);
lean_ctor_set(x_83, 3, x_36);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
x_84 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_84);
return x_1;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_41);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_41, 3);
lean_dec(x_86);
x_87 = lean_ctor_get(x_41, 0);
lean_dec(x_87);
x_88 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_88);
x_89 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_89);
return x_1;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_41, 1);
x_91 = lean_ctor_get(x_41, 2);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_42);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_43);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_92);
x_94 = 1;
lean_ctor_set(x_1, 0, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_94);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_41, 1);
x_98 = lean_ctor_get(x_41, 2);
x_99 = lean_ctor_get(x_41, 3);
x_100 = lean_ctor_get(x_41, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_42);
if (x_101 == 0)
{
uint8_t x_102; uint8_t x_103; 
x_102 = 1;
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_102);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_102);
x_103 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_103);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_42, 0);
x_105 = lean_ctor_get(x_42, 1);
x_106 = lean_ctor_get(x_42, 2);
x_107 = lean_ctor_get(x_42, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_42);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_108);
x_110 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_111 = lean_ctor_get(x_41, 1);
x_112 = lean_ctor_get(x_41, 2);
x_113 = lean_ctor_get(x_41, 3);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_41);
x_114 = lean_ctor_get(x_42, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_42, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_42, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_42, 3);
lean_inc(x_117);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_118 = x_42;
} else {
 lean_dec_ref(x_42);
 x_118 = lean_box(0);
}
x_119 = 1;
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(1, 4, 1);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_115);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_117);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_121, 0, x_113);
lean_ctor_set(x_121, 1, x_34);
lean_ctor_set(x_121, 2, x_35);
lean_ctor_set(x_121, 3, x_36);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_119);
x_122 = 0;
lean_ctor_set(x_1, 3, x_121);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_120);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_122);
return x_1;
}
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_41, 3);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_41, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_41, 0);
lean_dec(x_126);
x_127 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_128 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_128);
return x_1;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_41, 1);
x_130 = lean_ctor_get(x_41, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = 0;
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_42);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_131);
x_133 = 1;
lean_ctor_set(x_1, 0, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
}
else
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_123, sizeof(void*)*4);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_1);
x_135 = !lean_is_exclusive(x_41);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_41, 1);
x_137 = lean_ctor_get(x_41, 2);
x_138 = lean_ctor_get(x_41, 3);
lean_dec(x_138);
x_139 = lean_ctor_get(x_41, 0);
lean_dec(x_139);
x_140 = !lean_is_exclusive(x_123);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_123, 0);
x_142 = lean_ctor_get(x_123, 1);
x_143 = lean_ctor_get(x_123, 2);
x_144 = lean_ctor_get(x_123, 3);
x_145 = 1;
lean_inc(x_42);
lean_ctor_set(x_123, 3, x_141);
lean_ctor_set(x_123, 2, x_137);
lean_ctor_set(x_123, 1, x_136);
lean_ctor_set(x_123, 0, x_42);
x_146 = !lean_is_exclusive(x_42);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_42, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_42, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_42, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_42, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 0, x_144);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_145);
x_151 = 0;
lean_ctor_set(x_41, 3, x_42);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_151);
return x_41;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_42);
lean_ctor_set_uint8(x_123, sizeof(void*)*4, x_145);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_144);
lean_ctor_set(x_152, 1, x_34);
lean_ctor_set(x_152, 2, x_35);
lean_ctor_set(x_152, 3, x_36);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_145);
x_153 = 0;
lean_ctor_set(x_41, 3, x_152);
lean_ctor_set(x_41, 2, x_143);
lean_ctor_set(x_41, 1, x_142);
lean_ctor_set(x_41, 0, x_123);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_153);
return x_41;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_123, 0);
x_155 = lean_ctor_get(x_123, 1);
x_156 = lean_ctor_get(x_123, 2);
x_157 = lean_ctor_get(x_123, 3);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_123);
x_158 = 1;
lean_inc(x_42);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_42);
lean_ctor_set(x_159, 1, x_136);
lean_ctor_set(x_159, 2, x_137);
lean_ctor_set(x_159, 3, x_154);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_160 = x_42;
} else {
 lean_dec_ref(x_42);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_158);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_34);
lean_ctor_set(x_161, 2, x_35);
lean_ctor_set(x_161, 3, x_36);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_158);
x_162 = 0;
lean_ctor_set(x_41, 3, x_161);
lean_ctor_set(x_41, 2, x_156);
lean_ctor_set(x_41, 1, x_155);
lean_ctor_set(x_41, 0, x_159);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_162);
return x_41;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_163 = lean_ctor_get(x_41, 1);
x_164 = lean_ctor_get(x_41, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_41);
x_165 = lean_ctor_get(x_123, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_123, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_123, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 3);
lean_inc(x_168);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 x_169 = x_123;
} else {
 lean_dec_ref(x_123);
 x_169 = lean_box(0);
}
x_170 = 1;
lean_inc(x_42);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_42);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_172 = x_42;
} else {
 lean_dec_ref(x_42);
 x_172 = lean_box(0);
}
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_34);
lean_ctor_set(x_173, 2, x_35);
lean_ctor_set(x_173, 3, x_36);
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_170);
x_174 = 0;
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_167);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_174);
return x_175;
}
}
else
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_41);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_41, 3);
lean_dec(x_177);
x_178 = lean_ctor_get(x_41, 0);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_42);
if (x_179 == 0)
{
uint8_t x_180; uint8_t x_181; 
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_134);
x_180 = 0;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_180);
x_181 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_181);
return x_1;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; 
x_182 = lean_ctor_get(x_42, 0);
x_183 = lean_ctor_get(x_42, 1);
x_184 = lean_ctor_get(x_42, 2);
x_185 = lean_ctor_get(x_42, 3);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_42);
x_186 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_183);
lean_ctor_set(x_186, 2, x_184);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_134);
x_187 = 0;
lean_ctor_set(x_41, 0, x_186);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_187);
x_188 = 1;
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_189 = lean_ctor_get(x_41, 1);
x_190 = lean_ctor_get(x_41, 2);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_41);
x_191 = lean_ctor_get(x_42, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_42, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_42, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_42, 3);
lean_inc(x_194);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_195 = x_42;
} else {
 lean_dec_ref(x_42);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 4, 1);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_134);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_190);
lean_ctor_set(x_198, 3, x_123);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
}
case 1:
{
uint8_t x_200; 
lean_dec(x_35);
lean_dec(x_34);
x_200 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
default: 
{
uint8_t x_201; 
x_201 = l_Std_RBNode_isRed___rarg(x_36);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_36, x_2, x_3);
x_203 = 1;
lean_ctor_set(x_1, 3, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_203);
return x_1;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_36, x_2, x_3);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_204, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_204, 0);
lean_dec(x_209);
x_210 = 0;
lean_ctor_set(x_204, 0, x_206);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_210);
x_211 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_211);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_204, 1);
x_213 = lean_ctor_get(x_204, 2);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_204);
x_214 = 0;
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_206);
lean_ctor_set(x_215, 1, x_212);
lean_ctor_set(x_215, 2, x_213);
lean_ctor_set(x_215, 3, x_206);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = 1;
lean_ctor_set(x_1, 3, x_215);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_216);
return x_1;
}
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_204);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_204, 1);
x_220 = lean_ctor_get(x_204, 2);
x_221 = lean_ctor_get(x_204, 3);
lean_dec(x_221);
x_222 = lean_ctor_get(x_204, 0);
lean_dec(x_222);
x_223 = !lean_is_exclusive(x_206);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
x_226 = lean_ctor_get(x_206, 2);
x_227 = lean_ctor_get(x_206, 3);
x_228 = 1;
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 2, x_35);
lean_ctor_set(x_206, 1, x_34);
lean_ctor_set(x_206, 0, x_33);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_228);
lean_ctor_set(x_204, 3, x_227);
lean_ctor_set(x_204, 2, x_226);
lean_ctor_set(x_204, 1, x_225);
lean_ctor_set(x_204, 0, x_224);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_228);
x_229 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_229);
return x_1;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_ctor_get(x_206, 1);
x_232 = lean_ctor_get(x_206, 2);
x_233 = lean_ctor_get(x_206, 3);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = 1;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_34);
lean_ctor_set(x_235, 2, x_35);
lean_ctor_set(x_235, 3, x_205);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_204, 3, x_233);
lean_ctor_set(x_204, 2, x_232);
lean_ctor_set(x_204, 1, x_231);
lean_ctor_set(x_204, 0, x_230);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_234);
x_236 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_237 = lean_ctor_get(x_204, 1);
x_238 = lean_ctor_get(x_204, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_204);
x_239 = lean_ctor_get(x_206, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_206, 2);
lean_inc(x_241);
x_242 = lean_ctor_get(x_206, 3);
lean_inc(x_242);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_243 = x_206;
} else {
 lean_dec_ref(x_206);
 x_243 = lean_box(0);
}
x_244 = 1;
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(1, 4, 1);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_33);
lean_ctor_set(x_245, 1, x_34);
lean_ctor_set(x_245, 2, x_35);
lean_ctor_set(x_245, 3, x_205);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_242);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_244);
x_247 = 0;
lean_ctor_set(x_1, 3, x_246);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_247);
return x_1;
}
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_204, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_204, 0);
lean_dec(x_250);
x_251 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_251);
x_252 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; uint8_t x_257; 
x_253 = lean_ctor_get(x_204, 1);
x_254 = lean_ctor_get(x_204, 2);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_204);
x_255 = 0;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_205);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_206);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = 1;
lean_ctor_set(x_1, 3, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_257);
return x_1;
}
}
}
}
else
{
uint8_t x_258; 
x_258 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_204);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_204, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_205);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_205, 0);
x_263 = lean_ctor_get(x_205, 1);
x_264 = lean_ctor_get(x_205, 2);
x_265 = lean_ctor_get(x_205, 3);
x_266 = 1;
lean_ctor_set(x_205, 3, x_262);
lean_ctor_set(x_205, 2, x_35);
lean_ctor_set(x_205, 1, x_34);
lean_ctor_set(x_205, 0, x_33);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_266);
lean_ctor_set(x_204, 0, x_265);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_266);
x_267 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; 
x_268 = lean_ctor_get(x_205, 0);
x_269 = lean_ctor_get(x_205, 1);
x_270 = lean_ctor_get(x_205, 2);
x_271 = lean_ctor_get(x_205, 3);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_205);
x_272 = 1;
x_273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_273, 0, x_33);
lean_ctor_set(x_273, 1, x_34);
lean_ctor_set(x_273, 2, x_35);
lean_ctor_set(x_273, 3, x_268);
lean_ctor_set_uint8(x_273, sizeof(void*)*4, x_272);
lean_ctor_set(x_204, 0, x_271);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_272);
x_274 = 0;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_270);
lean_ctor_set(x_1, 1, x_269);
lean_ctor_set(x_1, 0, x_273);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_274);
return x_1;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_275 = lean_ctor_get(x_204, 1);
x_276 = lean_ctor_get(x_204, 2);
x_277 = lean_ctor_get(x_204, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_204);
x_278 = lean_ctor_get(x_205, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_205, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_205, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_205, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_282 = x_205;
} else {
 lean_dec_ref(x_205);
 x_282 = lean_box(0);
}
x_283 = 1;
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(1, 4, 1);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_33);
lean_ctor_set(x_284, 1, x_34);
lean_ctor_set(x_284, 2, x_35);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set_uint8(x_284, sizeof(void*)*4, x_283);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_275);
lean_ctor_set(x_285, 2, x_276);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = 0;
lean_ctor_set(x_1, 3, x_285);
lean_ctor_set(x_1, 2, x_280);
lean_ctor_set(x_1, 1, x_279);
lean_ctor_set(x_1, 0, x_284);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_286);
return x_1;
}
}
else
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_204, 3);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_204);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_289 = lean_ctor_get(x_204, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_204, 0);
lean_dec(x_290);
x_291 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_291);
x_292 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_292);
return x_1;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_204, 1);
x_294 = lean_ctor_get(x_204, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_204);
x_295 = 0;
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_205);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_295);
x_297 = 1;
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_297);
return x_1;
}
}
else
{
uint8_t x_298; 
x_298 = lean_ctor_get_uint8(x_287, sizeof(void*)*4);
if (x_298 == 0)
{
uint8_t x_299; 
lean_free_object(x_1);
x_299 = !lean_is_exclusive(x_204);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_204, 3);
lean_dec(x_300);
x_301 = lean_ctor_get(x_204, 0);
lean_dec(x_301);
x_302 = !lean_is_exclusive(x_287);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_303 = lean_ctor_get(x_287, 0);
x_304 = lean_ctor_get(x_287, 1);
x_305 = lean_ctor_get(x_287, 2);
x_306 = lean_ctor_get(x_287, 3);
x_307 = 1;
lean_inc(x_205);
lean_ctor_set(x_287, 3, x_205);
lean_ctor_set(x_287, 2, x_35);
lean_ctor_set(x_287, 1, x_34);
lean_ctor_set(x_287, 0, x_33);
x_308 = !lean_is_exclusive(x_205);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_205, 3);
lean_dec(x_309);
x_310 = lean_ctor_get(x_205, 2);
lean_dec(x_310);
x_311 = lean_ctor_get(x_205, 1);
lean_dec(x_311);
x_312 = lean_ctor_get(x_205, 0);
lean_dec(x_312);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
lean_ctor_set(x_205, 3, x_306);
lean_ctor_set(x_205, 2, x_305);
lean_ctor_set(x_205, 1, x_304);
lean_ctor_set(x_205, 0, x_303);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_307);
x_313 = 0;
lean_ctor_set(x_204, 3, x_205);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_313);
return x_204;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_205);
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_307);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_305);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_307);
x_315 = 0;
lean_ctor_set(x_204, 3, x_314);
lean_ctor_set(x_204, 0, x_287);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_315);
return x_204;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_316 = lean_ctor_get(x_287, 0);
x_317 = lean_ctor_get(x_287, 1);
x_318 = lean_ctor_get(x_287, 2);
x_319 = lean_ctor_get(x_287, 3);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_287);
x_320 = 1;
lean_inc(x_205);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_33);
lean_ctor_set(x_321, 1, x_34);
lean_ctor_set(x_321, 2, x_35);
lean_ctor_set(x_321, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_322 = x_205;
} else {
 lean_dec_ref(x_205);
 x_322 = lean_box(0);
}
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_316);
lean_ctor_set(x_323, 1, x_317);
lean_ctor_set(x_323, 2, x_318);
lean_ctor_set(x_323, 3, x_319);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_320);
x_324 = 0;
lean_ctor_set(x_204, 3, x_323);
lean_ctor_set(x_204, 0, x_321);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_324);
return x_204;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_325 = lean_ctor_get(x_204, 1);
x_326 = lean_ctor_get(x_204, 2);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_204);
x_327 = lean_ctor_get(x_287, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_287, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_287, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_287, 3);
lean_inc(x_330);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_331 = x_287;
} else {
 lean_dec_ref(x_287);
 x_331 = lean_box(0);
}
x_332 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_33);
lean_ctor_set(x_333, 1, x_34);
lean_ctor_set(x_333, 2, x_35);
lean_ctor_set(x_333, 3, x_205);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_334 = x_205;
} else {
 lean_dec_ref(x_205);
 x_334 = lean_box(0);
}
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_332);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_329);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_332);
x_336 = 0;
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_333);
lean_ctor_set(x_337, 1, x_325);
lean_ctor_set(x_337, 2, x_326);
lean_ctor_set(x_337, 3, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_336);
return x_337;
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_204);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_339 = lean_ctor_get(x_204, 3);
lean_dec(x_339);
x_340 = lean_ctor_get(x_204, 0);
lean_dec(x_340);
x_341 = !lean_is_exclusive(x_205);
if (x_341 == 0)
{
uint8_t x_342; uint8_t x_343; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_298);
x_342 = 0;
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_342);
x_343 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_344 = lean_ctor_get(x_205, 0);
x_345 = lean_ctor_get(x_205, 1);
x_346 = lean_ctor_get(x_205, 2);
x_347 = lean_ctor_get(x_205, 3);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_205);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_344);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_346);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_298);
x_349 = 0;
lean_ctor_set(x_204, 0, x_348);
lean_ctor_set_uint8(x_204, sizeof(void*)*4, x_349);
x_350 = 1;
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_350);
return x_1;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; 
x_351 = lean_ctor_get(x_204, 1);
x_352 = lean_ctor_get(x_204, 2);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_204);
x_353 = lean_ctor_get(x_205, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_205, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_205, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_205, 3);
lean_inc(x_356);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_357 = x_205;
} else {
 lean_dec_ref(x_205);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_353);
lean_ctor_set(x_358, 1, x_354);
lean_ctor_set(x_358, 2, x_355);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_298);
x_359 = 0;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_351);
lean_ctor_set(x_360, 2, x_352);
lean_ctor_set(x_360, 3, x_287);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
lean_ctor_set(x_1, 3, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
return x_1;
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
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_1, 0);
x_363 = lean_ctor_get(x_1, 1);
x_364 = lean_ctor_get(x_1, 2);
x_365 = lean_ctor_get(x_1, 3);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_1);
lean_inc(x_363);
lean_inc(x_2);
x_366 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_127_(x_2, x_363);
switch (x_366) {
case 0:
{
uint8_t x_367; 
x_367 = l_Std_RBNode_isRed___rarg(x_362);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_368 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_362, x_2, x_3);
x_369 = 1;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_363);
lean_ctor_set(x_370, 2, x_364);
lean_ctor_set(x_370, 3, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_362, x_2, x_3);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_371, 3);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
x_377 = 0;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_373);
lean_ctor_set(x_378, 1, x_374);
lean_ctor_set(x_378, 2, x_375);
lean_ctor_set(x_378, 3, x_373);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
x_379 = 1;
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_363);
lean_ctor_set(x_380, 2, x_364);
lean_ctor_set(x_380, 3, x_365);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
return x_380;
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
x_382 = lean_ctor_get(x_371, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_371, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_384 = x_371;
} else {
 lean_dec_ref(x_371);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_373, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_373, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_373, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 3);
lean_inc(x_388);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_389 = x_373;
} else {
 lean_dec_ref(x_373);
 x_389 = lean_box(0);
}
x_390 = 1;
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_372);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_383);
lean_ctor_set(x_391, 3, x_385);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_390);
if (lean_is_scalar(x_384)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_384;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_363);
lean_ctor_set(x_392, 2, x_364);
lean_ctor_set(x_392, 3, x_365);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_390);
x_393 = 0;
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_393);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_371, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_371, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_397 = x_371;
} else {
 lean_dec_ref(x_371);
 x_397 = lean_box(0);
}
x_398 = 0;
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_395);
lean_ctor_set(x_399, 2, x_396);
lean_ctor_set(x_399, 3, x_373);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_398);
x_400 = 1;
x_401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_363);
lean_ctor_set(x_401, 2, x_364);
lean_ctor_set(x_401, 3, x_365);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
return x_401;
}
}
}
else
{
uint8_t x_402; 
x_402 = lean_ctor_get_uint8(x_372, sizeof(void*)*4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_403 = lean_ctor_get(x_371, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_371, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_371, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_406 = x_371;
} else {
 lean_dec_ref(x_371);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_372, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_372, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_372, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_372, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_411 = x_372;
} else {
 lean_dec_ref(x_372);
 x_411 = lean_box(0);
}
x_412 = 1;
if (lean_is_scalar(x_411)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_411;
}
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_408);
lean_ctor_set(x_413, 2, x_409);
lean_ctor_set(x_413, 3, x_410);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
if (lean_is_scalar(x_406)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_406;
}
lean_ctor_set(x_414, 0, x_405);
lean_ctor_set(x_414, 1, x_363);
lean_ctor_set(x_414, 2, x_364);
lean_ctor_set(x_414, 3, x_365);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_412);
x_415 = 0;
x_416 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_403);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_415);
return x_416;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_371, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_371, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_371, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_420 = x_371;
} else {
 lean_dec_ref(x_371);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_372);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_363);
lean_ctor_set(x_424, 2, x_364);
lean_ctor_set(x_424, 3, x_365);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_426 = lean_ctor_get(x_371, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_371, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_428 = x_371;
} else {
 lean_dec_ref(x_371);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
lean_inc(x_372);
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_372);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_436 = x_372;
} else {
 lean_dec_ref(x_372);
 x_436 = lean_box(0);
}
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_363);
lean_ctor_set(x_437, 2, x_364);
lean_ctor_set(x_437, 3, x_365);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_434);
x_438 = 0;
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_435);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
return x_439;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_440 = lean_ctor_get(x_371, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_371, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 x_442 = x_371;
} else {
 lean_dec_ref(x_371);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_372, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_372, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_372, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_372, 3);
lean_inc(x_446);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 x_447 = x_372;
} else {
 lean_dec_ref(x_372);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_444);
lean_ctor_set(x_448, 2, x_445);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_425);
x_449 = 0;
if (lean_is_scalar(x_442)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_442;
}
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_440);
lean_ctor_set(x_450, 2, x_441);
lean_ctor_set(x_450, 3, x_417);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
x_451 = 1;
x_452 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_363);
lean_ctor_set(x_452, 2, x_364);
lean_ctor_set(x_452, 3, x_365);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
return x_452;
}
}
}
}
}
}
case 1:
{
uint8_t x_453; lean_object* x_454; 
lean_dec(x_364);
lean_dec(x_363);
x_453 = 1;
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_362);
lean_ctor_set(x_454, 1, x_2);
lean_ctor_set(x_454, 2, x_3);
lean_ctor_set(x_454, 3, x_365);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
default: 
{
uint8_t x_455; 
x_455 = l_Std_RBNode_isRed___rarg(x_365);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_456 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_365, x_2, x_3);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_362);
lean_ctor_set(x_458, 1, x_363);
lean_ctor_set(x_458, 2, x_364);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_365, x_2, x_3);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 3);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_464 = x_459;
} else {
 lean_dec_ref(x_459);
 x_464 = lean_box(0);
}
x_465 = 0;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_461);
lean_ctor_set(x_466, 1, x_462);
lean_ctor_set(x_466, 2, x_463);
lean_ctor_set(x_466, 3, x_461);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
x_467 = 1;
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_362);
lean_ctor_set(x_468, 1, x_363);
lean_ctor_set(x_468, 2, x_364);
lean_ctor_set(x_468, 3, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_461, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_470 = lean_ctor_get(x_459, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_472 = x_459;
} else {
 lean_dec_ref(x_459);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_461, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_461, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_461, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_461, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 lean_ctor_release(x_461, 2);
 lean_ctor_release(x_461, 3);
 x_477 = x_461;
} else {
 lean_dec_ref(x_461);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_362);
lean_ctor_set(x_479, 1, x_363);
lean_ctor_set(x_479, 2, x_364);
lean_ctor_set(x_479, 3, x_460);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_473);
lean_ctor_set(x_480, 1, x_474);
lean_ctor_set(x_480, 2, x_475);
lean_ctor_set(x_480, 3, x_476);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_471);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_459, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_459, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_485 = x_459;
} else {
 lean_dec_ref(x_459);
 x_485 = lean_box(0);
}
x_486 = 0;
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_460);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_461);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_486);
x_488 = 1;
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_362);
lean_ctor_set(x_489, 1, x_363);
lean_ctor_set(x_489, 2, x_364);
lean_ctor_set(x_489, 3, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
x_490 = lean_ctor_get_uint8(x_460, sizeof(void*)*4);
if (x_490 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_491 = lean_ctor_get(x_459, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_459, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_459, 3);
lean_inc(x_493);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_494 = x_459;
} else {
 lean_dec_ref(x_459);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_460, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_460, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_460, 2);
lean_inc(x_497);
x_498 = lean_ctor_get(x_460, 3);
lean_inc(x_498);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_499 = x_460;
} else {
 lean_dec_ref(x_460);
 x_499 = lean_box(0);
}
x_500 = 1;
if (lean_is_scalar(x_499)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_499;
}
lean_ctor_set(x_501, 0, x_362);
lean_ctor_set(x_501, 1, x_363);
lean_ctor_set(x_501, 2, x_364);
lean_ctor_set(x_501, 3, x_495);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
if (lean_is_scalar(x_494)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_494;
}
lean_ctor_set(x_502, 0, x_498);
lean_ctor_set(x_502, 1, x_491);
lean_ctor_set(x_502, 2, x_492);
lean_ctor_set(x_502, 3, x_493);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_500);
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_496);
lean_ctor_set(x_504, 2, x_497);
lean_ctor_set(x_504, 3, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_503);
return x_504;
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_459, 3);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_459, 2);
lean_inc(x_507);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_508 = x_459;
} else {
 lean_dec_ref(x_459);
 x_508 = lean_box(0);
}
x_509 = 0;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_460);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_505);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_509);
x_511 = 1;
x_512 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_512, 0, x_362);
lean_ctor_set(x_512, 1, x_363);
lean_ctor_set(x_512, 2, x_364);
lean_ctor_set(x_512, 3, x_510);
lean_ctor_set_uint8(x_512, sizeof(void*)*4, x_511);
return x_512;
}
else
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_505, sizeof(void*)*4);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_514 = lean_ctor_get(x_459, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_459, 2);
lean_inc(x_515);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_516 = x_459;
} else {
 lean_dec_ref(x_459);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_505, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_505, 2);
lean_inc(x_519);
x_520 = lean_ctor_get(x_505, 3);
lean_inc(x_520);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 x_521 = x_505;
} else {
 lean_dec_ref(x_505);
 x_521 = lean_box(0);
}
x_522 = 1;
lean_inc(x_460);
if (lean_is_scalar(x_521)) {
 x_523 = lean_alloc_ctor(1, 4, 1);
} else {
 x_523 = x_521;
}
lean_ctor_set(x_523, 0, x_362);
lean_ctor_set(x_523, 1, x_363);
lean_ctor_set(x_523, 2, x_364);
lean_ctor_set(x_523, 3, x_460);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_524 = x_460;
} else {
 lean_dec_ref(x_460);
 x_524 = lean_box(0);
}
lean_ctor_set_uint8(x_523, sizeof(void*)*4, x_522);
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 4, 1);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
lean_ctor_set(x_525, 3, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*4, x_522);
x_526 = 0;
if (lean_is_scalar(x_516)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_516;
}
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_514);
lean_ctor_set(x_527, 2, x_515);
lean_ctor_set(x_527, 3, x_525);
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_528 = lean_ctor_get(x_459, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_459, 2);
lean_inc(x_529);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_530 = x_459;
} else {
 lean_dec_ref(x_459);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_460, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_460, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_460, 2);
lean_inc(x_533);
x_534 = lean_ctor_get(x_460, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 lean_ctor_release(x_460, 2);
 lean_ctor_release(x_460, 3);
 x_535 = x_460;
} else {
 lean_dec_ref(x_460);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_531);
lean_ctor_set(x_536, 1, x_532);
lean_ctor_set(x_536, 2, x_533);
lean_ctor_set(x_536, 3, x_534);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_513);
x_537 = 0;
if (lean_is_scalar(x_530)) {
 x_538 = lean_alloc_ctor(1, 4, 1);
} else {
 x_538 = x_530;
}
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_528);
lean_ctor_set(x_538, 2, x_529);
lean_ctor_set(x_538, 3, x_505);
lean_ctor_set_uint8(x_538, sizeof(void*)*4, x_537);
x_539 = 1;
x_540 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_540, 0, x_362);
lean_ctor_set(x_540, 1, x_363);
lean_ctor_set(x_540, 2, x_364);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_539);
return x_540;
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
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__3(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_969_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot process request to closed file '", 39);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Server_Watchdog_findFileWorker_x3f(x_4, x_5, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1___closed__1;
x_26 = lean_string_append(x_25, x_4);
lean_dec(x_4);
x_27 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
x_30 = 7;
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_30);
x_32 = l_IO_FS_Stream_writeLspResponseError(x_24, x_31, x_23);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_45, 4);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_46, x_43);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_1);
x_50 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__1(x_1);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_50);
lean_free_object(x_22);
x_51 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_51);
lean_inc(x_2);
x_53 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__2(x_48, x_2, x_52);
x_54 = lean_st_ref_set(x_46, x_53, x_49);
lean_dec(x_46);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_7 = x_55;
goto block_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
lean_ctor_set(x_22, 0, x_56);
lean_inc(x_3);
lean_inc(x_2);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_3);
lean_ctor_set(x_57, 2, x_22);
lean_inc(x_2);
x_58 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__2(x_48, x_2, x_57);
x_59 = lean_st_ref_set(x_46, x_58, x_49);
lean_dec(x_46);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_7 = x_60;
goto block_20;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_22, 0);
lean_inc(x_61);
lean_dec(x_22);
x_62 = lean_ctor_get(x_61, 4);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_take(x_62, x_43);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_1);
x_66 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__1(x_1);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
x_67 = lean_box(0);
lean_inc(x_3);
lean_inc(x_2);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_3);
lean_ctor_set(x_68, 2, x_67);
lean_inc(x_2);
x_69 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__2(x_64, x_2, x_68);
x_70 = lean_st_ref_set(x_62, x_69, x_65);
lean_dec(x_62);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_7 = x_71;
goto block_20;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_inc(x_3);
lean_inc(x_2);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_3);
lean_ctor_set(x_74, 2, x_73);
lean_inc(x_2);
x_75 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__2(x_64, x_2, x_74);
x_76 = lean_st_ref_set(x_62, x_75, x_65);
lean_dec(x_62);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_7 = x_77;
goto block_20;
}
}
}
block_20:
{
lean_object* x_8; 
x_8 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__1(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = 1;
x_12 = 0;
x_13 = l_Lean_Server_Watchdog_tryWriteMessage(x_4, x_10, x_11, x_12, x_5, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_15);
x_17 = 1;
x_18 = 0;
x_19 = l_Lean_Server_Watchdog_tryWriteMessage(x_4, x_16, x_17, x_18, x_5, x_7);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/connect", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardRequestToWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1;
x_7 = lean_string_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Server_routeLspRequest(x_2, x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_11);
lean_dec(x_11);
x_14 = l_IO_FS_Stream_writeLspResponseError(x_12, x_13, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
lean_dec(x_9);
x_27 = l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1(x_3, x_1, x_2, x_26, x_4, x_25);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_inc(x_3);
x_28 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4(x_3, x_4, x_5);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1(x_3, x_1, x_2, x_29, x_4, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonWorkspaceSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2570_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonSymbolInformation____x40_Lean_Data_Lsp_LanguageFeatures___hyg_3319_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__3(x_7, x_8, x_5);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_IO_FS_Stream_writeLspMessage(x_1, x_11, x_3);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonReferenceParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_2432_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_934_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__6(x_7, x_8, x_5);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_IO_FS_Stream_writeLspMessage(x_1, x_11, x_3);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_2069_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/references", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspace/symbol", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\"", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed to process request ", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4;
x_2 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__7;
x_2 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__1;
x_8 = lean_string_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__2;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Server_Watchdog_forwardRequestToWorker(x_2, x_1, x_3, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_51; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_51 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(x_3, x_5, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Server_Watchdog_handleWorkspaceSymbol(x_52, x_5, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_55);
lean_inc(x_12);
x_58 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__2(x_12, x_57, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_dec(x_12);
lean_dec(x_2);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_13 = x_59;
x_14 = x_60;
goto block_50;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_13 = x_61;
x_14 = x_62;
goto block_50;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
x_63 = lean_ctor_get(x_51, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
lean_dec(x_51);
x_13 = x_63;
x_14 = x_64;
goto block_50;
}
block_50:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_io_error_to_string(x_13);
x_16 = lean_box(0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_19, x_18);
x_21 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec(x_15);
x_26 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = 4;
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
x_30 = l_IO_FS_Stream_writeLspResponseError(x_12, x_29, x_14);
lean_dec(x_29);
return x_30;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = l_Lean_JsonNumber_toString(x_31);
x_33 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_15);
lean_dec(x_15);
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_39 = lean_string_append(x_37, x_38);
x_40 = 4;
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_16);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
x_42 = l_IO_FS_Stream_writeLspResponseError(x_12, x_41, x_14);
lean_dec(x_41);
return x_42;
}
default: 
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_43 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8;
x_44 = lean_string_append(x_43, x_15);
lean_dec(x_15);
x_45 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_46 = lean_string_append(x_44, x_45);
x_47 = 4;
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
x_49 = l_IO_FS_Stream_writeLspResponseError(x_12, x_48, x_14);
lean_dec(x_48);
return x_49;
}
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_104; 
lean_dec(x_1);
x_65 = lean_ctor_get(x_5, 1);
lean_inc(x_65);
x_104 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__4(x_3, x_5, x_6);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Server_Watchdog_handleReference(x_105, x_5, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_2);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_2);
lean_ctor_set(x_110, 1, x_108);
lean_inc(x_65);
x_111 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__5(x_65, x_110, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_dec(x_65);
lean_dec(x_2);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_66 = x_112;
x_67 = x_113;
goto block_103;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_107, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
lean_dec(x_107);
x_66 = x_114;
x_67 = x_115;
goto block_103;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_5);
x_116 = lean_ctor_get(x_104, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_104, 1);
lean_inc(x_117);
lean_dec(x_104);
x_66 = x_116;
x_67 = x_117;
goto block_103;
}
block_103:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_io_error_to_string(x_66);
x_69 = lean_box(0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
x_71 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3;
x_72 = lean_string_append(x_71, x_70);
lean_dec(x_70);
x_73 = lean_string_append(x_72, x_71);
x_74 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_77, x_68);
lean_dec(x_68);
x_79 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_80 = lean_string_append(x_78, x_79);
x_81 = 4;
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_69);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_81);
x_83 = l_IO_FS_Stream_writeLspResponseError(x_65, x_82, x_67);
lean_dec(x_82);
return x_83;
}
case 1:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = l_Lean_JsonNumber_toString(x_84);
x_86 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_68);
lean_dec(x_68);
x_91 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_92 = lean_string_append(x_90, x_91);
x_93 = 4;
x_94 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_94, 0, x_2);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_69);
lean_ctor_set_uint8(x_94, sizeof(void*)*3, x_93);
x_95 = l_IO_FS_Stream_writeLspResponseError(x_65, x_94, x_67);
lean_dec(x_94);
return x_95;
}
default: 
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_96 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8;
x_97 = lean_string_append(x_96, x_68);
lean_dec(x_68);
x_98 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_99 = lean_string_append(x_97, x_98);
x_100 = 4;
x_101 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_69);
lean_ctor_set_uint8(x_101, sizeof(void*)*3, x_100);
x_102 = l_IO_FS_Stream_writeLspResponseError(x_65, x_101, x_67);
lean_dec(x_101);
return x_102;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/definition", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/declaration", 24);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_Watchdog_handleRequest___closed__1;
x_7 = lean_string_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_9 = lean_string_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_2, x_1, x_3, x_10, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc(x_3);
x_12 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_4);
x_15 = l_Lean_Server_Watchdog_findDefinitions(x_13, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_isEmpty___rarg(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_16);
x_21 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__5(x_19, x_20, x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
x_32 = lean_box(0);
x_33 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_2, x_1, x_3, x_32, x_4, x_17);
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
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; 
lean_inc(x_3);
x_42 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(x_3, x_4, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_4);
x_45 = l_Lean_Server_Watchdog_findDefinitions(x_43, x_4, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Array_isEmpty___rarg(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_dec(x_4);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_46);
x_51 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_handleRequest___spec__5(x_49, x_50, x_47);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_46);
x_62 = lean_box(0);
x_63 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_2, x_1, x_3, x_62, x_4, x_47);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_42);
if (x_68 == 0)
{
return x_42;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_42, 0);
x_70 = lean_ctor_get(x_42, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_42);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleRequest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_handleRequest___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_1512_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_1570_(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__3(x_2);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Server_Watchdog_tryWriteMessage(x_5, x_9, x_10, x_11, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_1366_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_1442_(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__6(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Server_Watchdog_tryWriteMessage(x_5, x_9, x_10, x_11, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1009_(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_2);
x_5 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__8(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = 1;
x_10 = 0;
x_11 = l_Lean_Server_Watchdog_tryWriteMessage(x_2, x_8, x_9, x_10, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_112_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonDidChangeWatchedFilesParams____x40_Lean_Data_Lsp_Workspace___hyg_575_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidCloseTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_649_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_146_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/didClose", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspace/didChangeWatchedFiles", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/release", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/keepAlive", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got unsupported notification: ", 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_handleNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_Watchdog_startFileWorker___closed__10;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_Watchdog_handleNotification___closed__1;
x_8 = lean_string_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Server_Watchdog_handleNotification___closed__2;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Server_Watchdog_handleNotification___closed__3;
x_16 = lean_string_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Server_Watchdog_handleNotification___closed__4;
x_18 = lean_string_dec_eq(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
x_19 = l_Lean_Server_Watchdog_handleNotification___closed__5;
x_20 = l_String_isPrefixOf(x_19, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
x_22 = l_Lean_Server_Watchdog_handleNotification___closed__6;
x_23 = lean_string_append(x_22, x_1);
lean_dec(x_1);
x_24 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_IO_FS_Stream_putStrLn(x_21, x_25, x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__1(x_2, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__2(x_1, x_30, x_3, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_1);
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
x_40 = l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__5(x_1, x_38, x_3, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_3);
lean_dec(x_1);
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
else
{
lean_object* x_45; 
x_45 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_forwardRequestToWorker___spec__4(x_2, x_3, x_4);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Server_Watchdog_forwardNotification___at_Lean_Server_Watchdog_handleNotification___spec__7(x_1, x_46, x_3, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
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
lean_object* x_53; 
lean_dec(x_1);
x_53 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__9(x_2, x_3, x_4);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Server_Watchdog_handleCancelRequest(x_54, x_3, x_55);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_1);
x_61 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__10(x_2, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Server_Watchdog_handleDidChangeWatchedFiles(x_62, x_3, x_63);
lean_dec(x_3);
lean_dec(x_62);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
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
lean_dec(x_1);
x_69 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__11(x_2, x_3, x_4);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Server_Watchdog_terminateFileWorker(x_70, x_3, x_71);
lean_dec(x_3);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_1);
x_77 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__12(x_2, x_3, x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Server_Watchdog_handleDidOpen(x_78, x_3, x_79);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
return x_77;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_77);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleNotification___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__10(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__11(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__12(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_7, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_io_wait(x_12, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_1 = x_9;
x_2 = x_15;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_7, x_2, x_3, x_4);
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
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Server_Watchdog_terminateFileWorker(x_8, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_1 = x_9;
x_2 = x_19;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_shutdown(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_15 = lean_box(0);
lean_inc(x_5);
x_16 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_5, x_15, x_1, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_7 = x_17;
goto block_14;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
block_14:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(0);
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_5, x_8, x_1, x_7);
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
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_shutdown(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_readLspMessage), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Server_Watchdog_runClientTask___closed__1;
x_6 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Task_Priority_default;
x_9 = lean_io_as_task(x_7, x_8, x_2);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Server_Watchdog_runClientTask___closed__2;
x_13 = lean_task_map(x_12, x_11, x_8);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = l_Lean_Server_Watchdog_runClientTask___closed__2;
x_17 = lean_task_map(x_16, x_14, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Watchdog_runClientTask___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_471_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Json_compress(x_1);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_parseParams___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("File changed.", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = l_Lean_Server_Watchdog_FileWorker_erasePendingRequest(x_1, x_18, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = 7;
x_24 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_23);
x_26 = l_IO_FS_Stream_writeLspResponseError(x_21, x_25, x_20);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_8 = x_28;
x_9 = x_27;
goto block_14;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_17);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_8 = x_33;
x_9 = x_7;
goto block_14;
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_18);
x_19 = l_Lean_Server_Watchdog_FileWorker_erasePendingRequest(x_1, x_18, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
x_22 = lean_box(0);
x_23 = 7;
x_24 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_23);
x_26 = l_IO_FS_Stream_writeLspResponseError(x_21, x_25, x_20);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_8 = x_28;
x_9 = x_27;
goto block_14;
}
else
{
uint8_t x_29; 
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_17);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1;
x_8 = x_33;
x_9 = x_7;
goto block_14;
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_4 = x_12;
x_5 = x_10;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5(x_7, x_2, x_3, x_4);
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
x_18 = lean_alloc_closure((void*)(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5___lambda__1), 2, 1);
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
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_mainLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
lean_inc(x_2);
x_4 = l_Lean_Server_Watchdog_runClientTask(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Server_Watchdog_mainLoop(x_5, x_2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Internal server error: got termination event for worker that should have been removed", 85);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO error while processing events for ", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("shutdown", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got invalid JSON-RPC message", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop___lambda__1), 3, 0);
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
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("register_ilean_watcher", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_mainLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_607 = lean_ctor_get(x_2, 4);
lean_inc(x_607);
x_608 = lean_st_ref_get(x_607, x_3);
lean_dec(x_607);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_612 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5(x_609, x_611, x_2, x_610);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_ctor_get(x_613, 0);
lean_inc(x_615);
lean_dec(x_613);
x_616 = lean_array_to_list(lean_box(0), x_615);
lean_inc(x_1);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_1);
lean_ctor_set(x_617, 1, x_616);
x_618 = lean_io_wait_any(x_617, x_614);
lean_dec(x_617);
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
lean_dec(x_618);
x_4 = x_619;
x_5 = x_620;
goto block_606;
block_606:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_2);
x_8 = l_Lean_Server_Watchdog_handleEdits(x_7, x_2, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Server_Watchdog_mainLoop___closed__1;
x_16 = l_IO_throwServerError___rarg(x_15, x_5);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_22 = l_Lean_Server_Watchdog_handleCrash(x_20, x_21, x_2, x_5);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_3 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Server_Watchdog_mainLoop___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_io_error_to_string(x_30);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_IO_throwServerError___rarg(x_41, x_5);
return x_42;
}
}
}
case 1:
{
lean_object* x_43; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_4, 0);
lean_inc(x_43);
lean_dec(x_4);
switch (lean_obj_tag(x_43)) {
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 2);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Server_Watchdog_mainLoop___closed__3;
x_48 = lean_string_dec_eq(x_45, x_47);
if (x_48 == 0)
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_2);
x_49 = l_Lean_Server_Watchdog_mainLoop___closed__4;
x_50 = l_IO_throwServerError___rarg(x_49, x_5);
return x_50;
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_2);
x_54 = l_Lean_Server_Watchdog_handleRequest(x_44, x_45, x_53, x_2, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_inc(x_2);
x_56 = l_Lean_Server_Watchdog_runClientTask(x_2, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_1 = x_57;
x_3 = x_58;
goto _start;
}
else
{
uint8_t x_60; 
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_54);
if (x_60 == 0)
{
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_54);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
lean_dec(x_51);
x_65 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_inc(x_2);
x_66 = l_Lean_Server_Watchdog_handleRequest(x_44, x_45, x_65, x_2, x_5);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
lean_inc(x_2);
x_68 = l_Lean_Server_Watchdog_runClientTask(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_1 = x_69;
x_3 = x_70;
goto _start;
}
else
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_66, 0);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_66);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_46);
lean_dec(x_45);
x_76 = l_Lean_Server_Watchdog_shutdown(x_2, x_5);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_44);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(x_78, x_80, x_77);
lean_dec(x_80);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_44);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_76);
if (x_82 == 0)
{
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_43, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_43, 1);
lean_inc(x_87);
lean_dec(x_43);
x_88 = l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1;
x_89 = lean_string_dec_eq(x_86, x_88);
if (x_89 == 0)
{
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_86);
lean_dec(x_2);
x_90 = l_Lean_Server_Watchdog_mainLoop___closed__4;
x_91 = l_IO_throwServerError___rarg(x_90, x_5);
return x_91;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_inc(x_2);
x_95 = l_Lean_Server_Watchdog_handleNotification(x_86, x_94, x_2, x_5);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_2);
x_97 = l_Lean_Server_Watchdog_runClientTask(x_2, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_1 = x_98;
x_3 = x_99;
goto _start;
}
else
{
uint8_t x_101; 
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_95);
if (x_101 == 0)
{
return x_95;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_95, 0);
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_95);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_92, 0);
lean_inc(x_105);
lean_dec(x_92);
x_106 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_inc(x_2);
x_107 = l_Lean_Server_Watchdog_handleNotification(x_86, x_106, x_2, x_5);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_2);
x_109 = l_Lean_Server_Watchdog_runClientTask(x_2, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_1 = x_110;
x_3 = x_111;
goto _start;
}
else
{
uint8_t x_113; 
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_107);
if (x_113 == 0)
{
return x_107;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_107, 0);
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_107);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
else
{
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
x_117 = l_Lean_Server_Watchdog_mainLoop___closed__4;
x_118 = l_IO_throwServerError___rarg(x_117, x_5);
return x_118;
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_87);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_87, 0);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_122, x_2, x_5);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = l_Lean_Server_Watchdog_findFileWorker_x21(x_128, x_2, x_125);
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_194; lean_object* x_195; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_io_mono_ms_now(x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_2, 6);
lean_inc(x_135);
x_136 = lean_nat_add(x_133, x_135);
lean_dec(x_135);
lean_dec(x_133);
x_137 = lean_ctor_get(x_130, 5);
lean_inc(x_137);
x_194 = lean_st_ref_take(x_137, x_134);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_127);
lean_dec(x_126);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_box(0);
x_198 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_199 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_200 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_200, 0, x_136);
lean_ctor_set(x_200, 1, x_124);
lean_ctor_set(x_200, 2, x_198);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_87, 0, x_200);
x_201 = lean_st_ref_set(x_137, x_87, x_196);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_138 = x_197;
x_139 = x_202;
goto block_193;
}
else
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_124);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_204 = lean_ctor_get(x_124, 1);
lean_dec(x_204);
x_205 = lean_ctor_get(x_124, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_195);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_195, 0);
x_208 = lean_ctor_get(x_194, 1);
lean_inc(x_208);
lean_dec(x_194);
x_209 = !lean_is_exclusive(x_207);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_207, 1);
x_211 = lean_ctor_get(x_207, 3);
x_212 = lean_ctor_get(x_207, 0);
lean_dec(x_212);
lean_ctor_set(x_195, 0, x_211);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = l_Array_append___rarg(x_213, x_127);
lean_ctor_set(x_124, 1, x_214);
x_215 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
lean_ctor_set(x_207, 3, x_215);
lean_ctor_set(x_207, 1, x_124);
lean_ctor_set(x_207, 0, x_136);
lean_ctor_set(x_87, 0, x_207);
x_216 = lean_st_ref_set(x_137, x_87, x_208);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_138 = x_195;
x_139 = x_217;
goto block_193;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_218 = lean_ctor_get(x_207, 1);
x_219 = lean_ctor_get(x_207, 2);
x_220 = lean_ctor_get(x_207, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_207);
lean_ctor_set(x_195, 0, x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = l_Array_append___rarg(x_221, x_127);
lean_ctor_set(x_124, 1, x_222);
x_223 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_224 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_224, 0, x_136);
lean_ctor_set(x_224, 1, x_124);
lean_ctor_set(x_224, 2, x_219);
lean_ctor_set(x_224, 3, x_223);
lean_ctor_set(x_87, 0, x_224);
x_225 = lean_st_ref_set(x_137, x_87, x_208);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
x_138 = x_195;
x_139 = x_226;
goto block_193;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_227 = lean_ctor_get(x_195, 0);
lean_inc(x_227);
lean_dec(x_195);
x_228 = lean_ctor_get(x_194, 1);
lean_inc(x_228);
lean_dec(x_194);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_227, 3);
lean_inc(x_231);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 lean_ctor_release(x_227, 3);
 x_232 = x_227;
} else {
 lean_dec_ref(x_227);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_231);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_dec(x_229);
x_235 = l_Array_append___rarg(x_234, x_127);
lean_ctor_set(x_124, 1, x_235);
x_236 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
if (lean_is_scalar(x_232)) {
 x_237 = lean_alloc_ctor(0, 4, 0);
} else {
 x_237 = x_232;
}
lean_ctor_set(x_237, 0, x_136);
lean_ctor_set(x_237, 1, x_124);
lean_ctor_set(x_237, 2, x_230);
lean_ctor_set(x_237, 3, x_236);
lean_ctor_set(x_87, 0, x_237);
x_238 = lean_st_ref_set(x_137, x_87, x_228);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_138 = x_233;
x_139 = x_239;
goto block_193;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_124);
x_240 = lean_ctor_get(x_195, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_241 = x_195;
} else {
 lean_dec_ref(x_195);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_194, 1);
lean_inc(x_242);
lean_dec(x_194);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_240, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_240, 3);
lean_inc(x_245);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 lean_ctor_release(x_240, 2);
 lean_ctor_release(x_240, 3);
 x_246 = x_240;
} else {
 lean_dec_ref(x_240);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_241;
}
lean_ctor_set(x_247, 0, x_245);
x_248 = lean_ctor_get(x_243, 1);
lean_inc(x_248);
lean_dec(x_243);
x_249 = l_Array_append___rarg(x_248, x_127);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_126);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
if (lean_is_scalar(x_246)) {
 x_252 = lean_alloc_ctor(0, 4, 0);
} else {
 x_252 = x_246;
}
lean_ctor_set(x_252, 0, x_136);
lean_ctor_set(x_252, 1, x_250);
lean_ctor_set(x_252, 2, x_244);
lean_ctor_set(x_252, 3, x_251);
lean_ctor_set(x_87, 0, x_252);
x_253 = lean_st_ref_set(x_137, x_87, x_242);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_138 = x_247;
x_139 = x_254;
goto block_193;
}
}
block_193:
{
lean_object* x_140; 
x_140 = l_Lean_Server_Watchdog_mainLoop___closed__5;
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_130, x_139);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_st_ref_take(x_137, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_142);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_box(0);
x_148 = lean_st_ref_set(x_137, x_147, x_146);
lean_dec(x_137);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_apply_3(x_140, x_149, x_2, x_150);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_145);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_145, 0);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
lean_dec(x_144);
x_155 = !lean_is_exclusive(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_153, 2);
lean_dec(x_156);
lean_ctor_set(x_153, 2, x_142);
x_157 = lean_st_ref_set(x_137, x_145, x_154);
lean_dec(x_137);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_apply_3(x_140, x_158, x_2, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_153, 0);
x_162 = lean_ctor_get(x_153, 1);
x_163 = lean_ctor_get(x_153, 3);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_153);
x_164 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
lean_ctor_set(x_164, 2, x_142);
lean_ctor_set(x_164, 3, x_163);
lean_ctor_set(x_145, 0, x_164);
x_165 = lean_st_ref_set(x_137, x_145, x_154);
lean_dec(x_137);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_apply_3(x_140, x_166, x_2, x_167);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_169 = lean_ctor_get(x_145, 0);
lean_inc(x_169);
lean_dec(x_145);
x_170 = lean_ctor_get(x_144, 1);
lean_inc(x_170);
lean_dec(x_144);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 3);
lean_inc(x_173);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 x_174 = x_169;
} else {
 lean_dec_ref(x_169);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(0, 4, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_172);
lean_ctor_set(x_175, 2, x_142);
lean_ctor_set(x_175, 3, x_173);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_st_ref_set(x_137, x_176, x_170);
lean_dec(x_137);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_apply_3(x_140, x_178, x_2, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; size_t x_183; size_t x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_137);
x_181 = lean_ctor_get(x_138, 0);
lean_inc(x_181);
lean_dec(x_138);
x_182 = lean_array_get_size(x_181);
x_183 = lean_usize_of_nat(x_182);
lean_dec(x_182);
x_184 = 0;
x_185 = lean_box(0);
lean_inc(x_2);
x_186 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3(x_130, x_181, x_183, x_184, x_185, x_2, x_139);
lean_dec(x_181);
lean_dec(x_130);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_apply_3(x_140, x_185, x_2, x_187);
return x_188;
}
else
{
uint8_t x_189; 
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
return x_186;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_186, 0);
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_186);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_124);
lean_free_object(x_87);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_129);
if (x_255 == 0)
{
return x_129;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_129, 0);
x_257 = lean_ctor_get(x_129, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_129);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
uint8_t x_259; 
lean_free_object(x_87);
lean_dec(x_2);
x_259 = !lean_is_exclusive(x_123);
if (x_259 == 0)
{
return x_123;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_123, 0);
x_261 = lean_ctor_get(x_123, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_123);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_120, 0);
lean_inc(x_263);
lean_dec(x_120);
x_264 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_264, 0, x_263);
x_265 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_264, x_2, x_5);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 0);
lean_inc(x_270);
x_271 = l_Lean_Server_Watchdog_findFileWorker_x21(x_270, x_2, x_267);
lean_dec(x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_336; lean_object* x_337; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_io_mono_ms_now(x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_277 = lean_ctor_get(x_2, 6);
lean_inc(x_277);
x_278 = lean_nat_add(x_275, x_277);
lean_dec(x_277);
lean_dec(x_275);
x_279 = lean_ctor_get(x_272, 5);
lean_inc(x_279);
x_336 = lean_st_ref_take(x_279, x_276);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_269);
lean_dec(x_268);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_box(0);
x_340 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_341 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_342 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_342, 0, x_278);
lean_ctor_set(x_342, 1, x_266);
lean_ctor_set(x_342, 2, x_340);
lean_ctor_set(x_342, 3, x_341);
lean_ctor_set(x_87, 0, x_342);
x_343 = lean_st_ref_set(x_279, x_87, x_338);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_280 = x_339;
x_281 = x_344;
goto block_335;
}
else
{
uint8_t x_345; 
x_345 = !lean_is_exclusive(x_266);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_346 = lean_ctor_get(x_266, 1);
lean_dec(x_346);
x_347 = lean_ctor_get(x_266, 0);
lean_dec(x_347);
x_348 = !lean_is_exclusive(x_337);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_349 = lean_ctor_get(x_337, 0);
x_350 = lean_ctor_get(x_336, 1);
lean_inc(x_350);
lean_dec(x_336);
x_351 = !lean_is_exclusive(x_349);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_352 = lean_ctor_get(x_349, 1);
x_353 = lean_ctor_get(x_349, 3);
x_354 = lean_ctor_get(x_349, 0);
lean_dec(x_354);
lean_ctor_set(x_337, 0, x_353);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
x_356 = l_Array_append___rarg(x_355, x_269);
lean_ctor_set(x_266, 1, x_356);
x_357 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
lean_ctor_set(x_349, 3, x_357);
lean_ctor_set(x_349, 1, x_266);
lean_ctor_set(x_349, 0, x_278);
lean_ctor_set(x_87, 0, x_349);
x_358 = lean_st_ref_set(x_279, x_87, x_350);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_280 = x_337;
x_281 = x_359;
goto block_335;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_360 = lean_ctor_get(x_349, 1);
x_361 = lean_ctor_get(x_349, 2);
x_362 = lean_ctor_get(x_349, 3);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_349);
lean_ctor_set(x_337, 0, x_362);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
lean_dec(x_360);
x_364 = l_Array_append___rarg(x_363, x_269);
lean_ctor_set(x_266, 1, x_364);
x_365 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_366 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_366, 0, x_278);
lean_ctor_set(x_366, 1, x_266);
lean_ctor_set(x_366, 2, x_361);
lean_ctor_set(x_366, 3, x_365);
lean_ctor_set(x_87, 0, x_366);
x_367 = lean_st_ref_set(x_279, x_87, x_350);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_280 = x_337;
x_281 = x_368;
goto block_335;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_369 = lean_ctor_get(x_337, 0);
lean_inc(x_369);
lean_dec(x_337);
x_370 = lean_ctor_get(x_336, 1);
lean_inc(x_370);
lean_dec(x_336);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_369, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_369, 3);
lean_inc(x_373);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 x_374 = x_369;
} else {
 lean_dec_ref(x_369);
 x_374 = lean_box(0);
}
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_373);
x_376 = lean_ctor_get(x_371, 1);
lean_inc(x_376);
lean_dec(x_371);
x_377 = l_Array_append___rarg(x_376, x_269);
lean_ctor_set(x_266, 1, x_377);
x_378 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
if (lean_is_scalar(x_374)) {
 x_379 = lean_alloc_ctor(0, 4, 0);
} else {
 x_379 = x_374;
}
lean_ctor_set(x_379, 0, x_278);
lean_ctor_set(x_379, 1, x_266);
lean_ctor_set(x_379, 2, x_372);
lean_ctor_set(x_379, 3, x_378);
lean_ctor_set(x_87, 0, x_379);
x_380 = lean_st_ref_set(x_279, x_87, x_370);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_280 = x_375;
x_281 = x_381;
goto block_335;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_266);
x_382 = lean_ctor_get(x_337, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_383 = x_337;
} else {
 lean_dec_ref(x_337);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_336, 1);
lean_inc(x_384);
lean_dec(x_336);
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_382, 2);
lean_inc(x_386);
x_387 = lean_ctor_get(x_382, 3);
lean_inc(x_387);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 lean_ctor_release(x_382, 2);
 lean_ctor_release(x_382, 3);
 x_388 = x_382;
} else {
 lean_dec_ref(x_382);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_389 = x_383;
}
lean_ctor_set(x_389, 0, x_387);
x_390 = lean_ctor_get(x_385, 1);
lean_inc(x_390);
lean_dec(x_385);
x_391 = l_Array_append___rarg(x_390, x_269);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_268);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
if (lean_is_scalar(x_388)) {
 x_394 = lean_alloc_ctor(0, 4, 0);
} else {
 x_394 = x_388;
}
lean_ctor_set(x_394, 0, x_278);
lean_ctor_set(x_394, 1, x_392);
lean_ctor_set(x_394, 2, x_386);
lean_ctor_set(x_394, 3, x_393);
lean_ctor_set(x_87, 0, x_394);
x_395 = lean_st_ref_set(x_279, x_87, x_384);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_280 = x_389;
x_281 = x_396;
goto block_335;
}
}
block_335:
{
lean_object* x_282; 
x_282 = l_Lean_Server_Watchdog_mainLoop___closed__5;
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_272, x_281);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_st_ref_take(x_279, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_284);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_box(0);
x_290 = lean_st_ref_set(x_279, x_289, x_288);
lean_dec(x_279);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_apply_3(x_282, x_291, x_2, x_292);
return x_293;
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_287);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_287, 0);
x_296 = lean_ctor_get(x_286, 1);
lean_inc(x_296);
lean_dec(x_286);
x_297 = !lean_is_exclusive(x_295);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_295, 2);
lean_dec(x_298);
lean_ctor_set(x_295, 2, x_284);
x_299 = lean_st_ref_set(x_279, x_287, x_296);
lean_dec(x_279);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_apply_3(x_282, x_300, x_2, x_301);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_303 = lean_ctor_get(x_295, 0);
x_304 = lean_ctor_get(x_295, 1);
x_305 = lean_ctor_get(x_295, 3);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_295);
x_306 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
lean_ctor_set(x_306, 2, x_284);
lean_ctor_set(x_306, 3, x_305);
lean_ctor_set(x_287, 0, x_306);
x_307 = lean_st_ref_set(x_279, x_287, x_296);
lean_dec(x_279);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_apply_3(x_282, x_308, x_2, x_309);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_311 = lean_ctor_get(x_287, 0);
lean_inc(x_311);
lean_dec(x_287);
x_312 = lean_ctor_get(x_286, 1);
lean_inc(x_312);
lean_dec(x_286);
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_311, 3);
lean_inc(x_315);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 lean_ctor_release(x_311, 2);
 lean_ctor_release(x_311, 3);
 x_316 = x_311;
} else {
 lean_dec_ref(x_311);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(0, 4, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_313);
lean_ctor_set(x_317, 1, x_314);
lean_ctor_set(x_317, 2, x_284);
lean_ctor_set(x_317, 3, x_315);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = lean_st_ref_set(x_279, x_318, x_312);
lean_dec(x_279);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_apply_3(x_282, x_320, x_2, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; size_t x_325; size_t x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_279);
x_323 = lean_ctor_get(x_280, 0);
lean_inc(x_323);
lean_dec(x_280);
x_324 = lean_array_get_size(x_323);
x_325 = lean_usize_of_nat(x_324);
lean_dec(x_324);
x_326 = 0;
x_327 = lean_box(0);
lean_inc(x_2);
x_328 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4(x_272, x_323, x_325, x_326, x_327, x_2, x_281);
lean_dec(x_323);
lean_dec(x_272);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_apply_3(x_282, x_327, x_2, x_329);
return x_330;
}
else
{
uint8_t x_331; 
lean_dec(x_2);
x_331 = !lean_is_exclusive(x_328);
if (x_331 == 0)
{
return x_328;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_328, 0);
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_328);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_266);
lean_free_object(x_87);
lean_dec(x_2);
x_397 = !lean_is_exclusive(x_271);
if (x_397 == 0)
{
return x_271;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_271, 0);
x_399 = lean_ctor_get(x_271, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_271);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
uint8_t x_401; 
lean_free_object(x_87);
lean_dec(x_2);
x_401 = !lean_is_exclusive(x_265);
if (x_401 == 0)
{
return x_265;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_265, 0);
x_403 = lean_ctor_get(x_265, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_265);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
}
else
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_87, 0);
lean_inc(x_405);
lean_dec(x_87);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec(x_405);
x_407 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_407, 0, x_406);
x_408 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_407, x_2, x_5);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
x_414 = l_Lean_Server_Watchdog_findFileWorker_x21(x_413, x_2, x_410);
lean_dec(x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_463; lean_object* x_464; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_io_mono_ms_now(x_416);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_2, 6);
lean_inc(x_420);
x_421 = lean_nat_add(x_418, x_420);
lean_dec(x_420);
lean_dec(x_418);
x_422 = lean_ctor_get(x_415, 5);
lean_inc(x_422);
x_463 = lean_st_ref_take(x_422, x_419);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_412);
lean_dec(x_411);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = lean_box(0);
x_467 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_468 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_469 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_469, 0, x_421);
lean_ctor_set(x_469, 1, x_409);
lean_ctor_set(x_469, 2, x_467);
lean_ctor_set(x_469, 3, x_468);
x_470 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_470, 0, x_469);
x_471 = lean_st_ref_set(x_422, x_470, x_465);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
lean_dec(x_471);
x_423 = x_466;
x_424 = x_472;
goto block_462;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_473 = x_409;
} else {
 lean_dec_ref(x_409);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_464, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_475 = x_464;
} else {
 lean_dec_ref(x_464);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_463, 1);
lean_inc(x_476);
lean_dec(x_463);
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
x_478 = lean_ctor_get(x_474, 2);
lean_inc(x_478);
x_479 = lean_ctor_get(x_474, 3);
lean_inc(x_479);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 lean_ctor_release(x_474, 2);
 lean_ctor_release(x_474, 3);
 x_480 = x_474;
} else {
 lean_dec_ref(x_474);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_481 = lean_alloc_ctor(1, 1, 0);
} else {
 x_481 = x_475;
}
lean_ctor_set(x_481, 0, x_479);
x_482 = lean_ctor_get(x_477, 1);
lean_inc(x_482);
lean_dec(x_477);
x_483 = l_Array_append___rarg(x_482, x_412);
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_411);
lean_ctor_set(x_484, 1, x_483);
x_485 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
if (lean_is_scalar(x_480)) {
 x_486 = lean_alloc_ctor(0, 4, 0);
} else {
 x_486 = x_480;
}
lean_ctor_set(x_486, 0, x_421);
lean_ctor_set(x_486, 1, x_484);
lean_ctor_set(x_486, 2, x_478);
lean_ctor_set(x_486, 3, x_485);
x_487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_st_ref_set(x_422, x_487, x_476);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec(x_488);
x_423 = x_481;
x_424 = x_489;
goto block_462;
}
block_462:
{
lean_object* x_425; 
x_425 = l_Lean_Server_Watchdog_mainLoop___closed__5;
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_426 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_415, x_424);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_st_ref_take(x_422, x_428);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_427);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_box(0);
x_433 = lean_st_ref_set(x_422, x_432, x_431);
lean_dec(x_422);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_apply_3(x_425, x_434, x_2, x_435);
return x_436;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_437 = lean_ctor_get(x_430, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_438 = x_430;
} else {
 lean_dec_ref(x_430);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_429, 1);
lean_inc(x_439);
lean_dec(x_429);
x_440 = lean_ctor_get(x_437, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_437, 1);
lean_inc(x_441);
x_442 = lean_ctor_get(x_437, 3);
lean_inc(x_442);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 lean_ctor_release(x_437, 2);
 lean_ctor_release(x_437, 3);
 x_443 = x_437;
} else {
 lean_dec_ref(x_437);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(0, 4, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_440);
lean_ctor_set(x_444, 1, x_441);
lean_ctor_set(x_444, 2, x_427);
lean_ctor_set(x_444, 3, x_442);
if (lean_is_scalar(x_438)) {
 x_445 = lean_alloc_ctor(1, 1, 0);
} else {
 x_445 = x_438;
}
lean_ctor_set(x_445, 0, x_444);
x_446 = lean_st_ref_set(x_422, x_445, x_439);
lean_dec(x_422);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
x_449 = lean_apply_3(x_425, x_447, x_2, x_448);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; size_t x_452; size_t x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_422);
x_450 = lean_ctor_get(x_423, 0);
lean_inc(x_450);
lean_dec(x_423);
x_451 = lean_array_get_size(x_450);
x_452 = lean_usize_of_nat(x_451);
lean_dec(x_451);
x_453 = 0;
x_454 = lean_box(0);
lean_inc(x_2);
x_455 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3(x_415, x_450, x_452, x_453, x_454, x_2, x_424);
lean_dec(x_450);
lean_dec(x_415);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
lean_dec(x_455);
x_457 = lean_apply_3(x_425, x_454, x_2, x_456);
return x_457;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_2);
x_458 = lean_ctor_get(x_455, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_455, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_460 = x_455;
} else {
 lean_dec_ref(x_455);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
}
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_2);
x_490 = lean_ctor_get(x_414, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_414, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_492 = x_414;
} else {
 lean_dec_ref(x_414);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_2);
x_494 = lean_ctor_get(x_408, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_408, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_496 = x_408;
} else {
 lean_dec_ref(x_408);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_405, 0);
lean_inc(x_498);
lean_dec(x_405);
x_499 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_499, 0, x_498);
x_500 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_499, x_2, x_5);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 0);
lean_inc(x_505);
x_506 = l_Lean_Server_Watchdog_findFileWorker_x21(x_505, x_2, x_502);
lean_dec(x_505);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_555; lean_object* x_556; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_io_mono_ms_now(x_508);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_512 = lean_ctor_get(x_2, 6);
lean_inc(x_512);
x_513 = lean_nat_add(x_510, x_512);
lean_dec(x_512);
lean_dec(x_510);
x_514 = lean_ctor_get(x_507, 5);
lean_inc(x_514);
x_555 = lean_st_ref_take(x_514, x_511);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_504);
lean_dec(x_503);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_box(0);
x_559 = l_Lean_Server_Watchdog_mainLoop___closed__6;
x_560 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_561 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_561, 0, x_513);
lean_ctor_set(x_561, 1, x_501);
lean_ctor_set(x_561, 2, x_559);
lean_ctor_set(x_561, 3, x_560);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_561);
x_563 = lean_st_ref_set(x_514, x_562, x_557);
x_564 = lean_ctor_get(x_563, 1);
lean_inc(x_564);
lean_dec(x_563);
x_515 = x_558;
x_516 = x_564;
goto block_554;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_565 = x_501;
} else {
 lean_dec_ref(x_501);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_556, 0);
lean_inc(x_566);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 x_567 = x_556;
} else {
 lean_dec_ref(x_556);
 x_567 = lean_box(0);
}
x_568 = lean_ctor_get(x_555, 1);
lean_inc(x_568);
lean_dec(x_555);
x_569 = lean_ctor_get(x_566, 1);
lean_inc(x_569);
x_570 = lean_ctor_get(x_566, 2);
lean_inc(x_570);
x_571 = lean_ctor_get(x_566, 3);
lean_inc(x_571);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 lean_ctor_release(x_566, 2);
 lean_ctor_release(x_566, 3);
 x_572 = x_566;
} else {
 lean_dec_ref(x_566);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_573 = lean_alloc_ctor(1, 1, 0);
} else {
 x_573 = x_567;
}
lean_ctor_set(x_573, 0, x_571);
x_574 = lean_ctor_get(x_569, 1);
lean_inc(x_574);
lean_dec(x_569);
x_575 = l_Array_append___rarg(x_574, x_504);
if (lean_is_scalar(x_565)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_565;
}
lean_ctor_set(x_576, 0, x_503);
lean_ctor_set(x_576, 1, x_575);
x_577 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
if (lean_is_scalar(x_572)) {
 x_578 = lean_alloc_ctor(0, 4, 0);
} else {
 x_578 = x_572;
}
lean_ctor_set(x_578, 0, x_513);
lean_ctor_set(x_578, 1, x_576);
lean_ctor_set(x_578, 2, x_570);
lean_ctor_set(x_578, 3, x_577);
x_579 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_579, 0, x_578);
x_580 = lean_st_ref_set(x_514, x_579, x_568);
x_581 = lean_ctor_get(x_580, 1);
lean_inc(x_581);
lean_dec(x_580);
x_515 = x_573;
x_516 = x_581;
goto block_554;
}
block_554:
{
lean_object* x_517; 
x_517 = l_Lean_Server_Watchdog_mainLoop___closed__5;
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_518 = l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask(x_507, x_516);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = lean_st_ref_take(x_514, x_520);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_519);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_box(0);
x_525 = lean_st_ref_set(x_514, x_524, x_523);
lean_dec(x_514);
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
x_528 = lean_apply_3(x_517, x_526, x_2, x_527);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_529 = lean_ctor_get(x_522, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 x_530 = x_522;
} else {
 lean_dec_ref(x_522);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_521, 1);
lean_inc(x_531);
lean_dec(x_521);
x_532 = lean_ctor_get(x_529, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_529, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_529, 3);
lean_inc(x_534);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 lean_ctor_release(x_529, 2);
 lean_ctor_release(x_529, 3);
 x_535 = x_529;
} else {
 lean_dec_ref(x_529);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(0, 4, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_532);
lean_ctor_set(x_536, 1, x_533);
lean_ctor_set(x_536, 2, x_519);
lean_ctor_set(x_536, 3, x_534);
if (lean_is_scalar(x_530)) {
 x_537 = lean_alloc_ctor(1, 1, 0);
} else {
 x_537 = x_530;
}
lean_ctor_set(x_537, 0, x_536);
x_538 = lean_st_ref_set(x_514, x_537, x_531);
lean_dec(x_514);
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_apply_3(x_517, x_539, x_2, x_540);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; size_t x_544; size_t x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_514);
x_542 = lean_ctor_get(x_515, 0);
lean_inc(x_542);
lean_dec(x_515);
x_543 = lean_array_get_size(x_542);
x_544 = lean_usize_of_nat(x_543);
lean_dec(x_543);
x_545 = 0;
x_546 = lean_box(0);
lean_inc(x_2);
x_547 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4(x_507, x_542, x_544, x_545, x_546, x_2, x_516);
lean_dec(x_542);
lean_dec(x_507);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; 
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
lean_dec(x_547);
x_549 = lean_apply_3(x_517, x_546, x_2, x_548);
return x_549;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_2);
x_550 = lean_ctor_get(x_547, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_547, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_552 = x_547;
} else {
 lean_dec_ref(x_547);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_551);
return x_553;
}
}
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_501);
lean_dec(x_2);
x_582 = lean_ctor_get(x_506, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_506, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_584 = x_506;
} else {
 lean_dec_ref(x_506);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
return x_585;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_2);
x_586 = lean_ctor_get(x_500, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_500, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_588 = x_500;
} else {
 lean_dec_ref(x_500);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_586);
lean_ctor_set(x_589, 1, x_587);
return x_589;
}
}
}
}
}
}
case 2:
{
lean_object* x_590; 
x_590 = lean_ctor_get(x_43, 0);
lean_inc(x_590);
lean_dec(x_43);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; uint8_t x_593; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec(x_590);
x_592 = l_Lean_Server_Watchdog_mainLoop___closed__7;
x_593 = lean_string_dec_eq(x_591, x_592);
lean_dec(x_591);
if (x_593 == 0)
{
lean_object* x_594; lean_object* x_595; 
lean_dec(x_2);
x_594 = l_Lean_Server_Watchdog_mainLoop___closed__4;
x_595 = l_IO_throwServerError___rarg(x_594, x_5);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_inc(x_2);
x_596 = l_Lean_Server_Watchdog_runClientTask(x_2, x_5);
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
x_1 = x_597;
x_3 = x_598;
goto _start;
}
}
else
{
lean_object* x_600; lean_object* x_601; 
lean_dec(x_590);
lean_dec(x_2);
x_600 = l_Lean_Server_Watchdog_mainLoop___closed__4;
x_601 = l_IO_throwServerError___rarg(x_600, x_5);
return x_601;
}
}
default: 
{
lean_object* x_602; lean_object* x_603; 
lean_dec(x_43);
lean_dec(x_2);
x_602 = l_Lean_Server_Watchdog_mainLoop___closed__4;
x_603 = l_IO_throwServerError___rarg(x_602, x_5);
return x_603;
}
}
}
default: 
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_2);
lean_dec(x_1);
x_604 = lean_ctor_get(x_4, 0);
lean_inc(x_604);
lean_dec(x_4);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_5);
return x_605;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_mainLoop___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__4(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_mainLoop___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
x_1 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
x_2 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
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
x_2 = l_Lean_Lsp_SemanticTokenModifier_names;
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
x_5 = lean_alloc_ctor(0, 3, 9);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 4, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 5, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 6, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 7, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 8, x_3);
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
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC notification, got: '", 38);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected method '", 17);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', got method '", 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
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
x_21 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l_List_appendTR___rarg(x_23, x_18);
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = l_Lean_Json_compress(x_27);
x_29 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_36 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
x_39 = l_List_appendTR___rarg(x_38, x_18);
x_40 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_mkObj(x_41);
x_43 = l_Lean_Json_compress(x_42);
x_44 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_49 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
x_51 = l_List_appendTR___rarg(x_50, x_18);
x_52 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Json_mkObj(x_53);
x_55 = l_Lean_Json_compress(x_54);
x_56 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_66 = l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
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
x_74 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = l_List_appendTR___rarg(x_76, x_71);
x_78 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = l_Lean_Json_compress(x_80);
x_82 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_90 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_69);
x_93 = l_List_appendTR___rarg(x_92, x_71);
x_94 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Json_mkObj(x_95);
x_97 = l_Lean_Json_compress(x_96);
x_98 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_104 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_69);
x_106 = l_List_appendTR___rarg(x_105, x_71);
x_107 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_Lean_Json_compress(x_109);
x_111 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_121 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2;
x_122 = lean_string_append(x_121, x_3);
lean_dec(x_3);
x_123 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_string_append(x_124, x_119);
lean_dec(x_119);
x_126 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_134 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2;
x_135 = lean_string_append(x_134, x_3);
lean_dec(x_3);
x_136 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3;
x_137 = lean_string_append(x_135, x_136);
x_138 = lean_string_append(x_137, x_132);
lean_dec(x_132);
x_139 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_150 = l_Lean_Server_Watchdog_tryWriteMessage___closed__12;
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
x_156 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
x_159 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Json_mkObj(x_160);
x_162 = l_Lean_Json_compress(x_161);
x_163 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_170 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_153);
x_173 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Lean_Json_mkObj(x_174);
x_176 = l_Lean_Json_compress(x_175);
x_177 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_178 = lean_string_append(x_177, x_176);
lean_dec(x_176);
x_179 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_182 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_153);
x_184 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = l_Lean_Json_mkObj(x_185);
x_187 = l_Lean_Json_compress(x_186);
x_188 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_196 = l_Lean_Server_Watchdog_tryWriteMessage___closed__12;
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
x_202 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_199);
x_205 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_Json_mkObj(x_206);
x_208 = l_Lean_Json_compress(x_207);
x_209 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_210 = lean_string_append(x_209, x_208);
lean_dec(x_208);
x_211 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_217 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_199);
x_220 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l_Lean_Json_mkObj(x_221);
x_223 = l_Lean_Json_compress(x_222);
x_224 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_225 = lean_string_append(x_224, x_223);
lean_dec(x_223);
x_226 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_230 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_199);
x_232 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l_Lean_Json_mkObj(x_233);
x_235 = l_Lean_Json_compress(x_234);
x_236 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_237 = lean_string_append(x_236, x_235);
lean_dec(x_235);
x_238 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
x_249 = l_Lean_Server_Watchdog_tryWriteMessage___closed__13;
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_Server_Watchdog_tryWriteMessage___closed__14;
x_254 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_253, x_247);
lean_dec(x_247);
switch (lean_obj_tag(x_244)) {
case 0:
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_244, 0);
lean_inc(x_292);
lean_dec(x_244);
x_293 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_255 = x_293;
goto block_291;
}
case 1:
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_244, 0);
lean_inc(x_294);
lean_dec(x_244);
x_295 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_295, 0, x_294);
x_255 = x_295;
goto block_291;
}
default: 
{
lean_object* x_296; 
x_296 = lean_box(0);
x_255 = x_296;
goto block_291;
}
}
block_291:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
switch (x_245) {
case 0:
{
lean_object* x_279; 
x_279 = l_Lean_Server_Watchdog_tryWriteMessage___closed__20;
x_258 = x_279;
goto block_278;
}
case 1:
{
lean_object* x_280; 
x_280 = l_Lean_Server_Watchdog_tryWriteMessage___closed__24;
x_258 = x_280;
goto block_278;
}
case 2:
{
lean_object* x_281; 
x_281 = l_Lean_Server_Watchdog_tryWriteMessage___closed__28;
x_258 = x_281;
goto block_278;
}
case 3:
{
lean_object* x_282; 
x_282 = l_Lean_Server_Watchdog_tryWriteMessage___closed__32;
x_258 = x_282;
goto block_278;
}
case 4:
{
lean_object* x_283; 
x_283 = l_Lean_Server_Watchdog_tryWriteMessage___closed__36;
x_258 = x_283;
goto block_278;
}
case 5:
{
lean_object* x_284; 
x_284 = l_Lean_Server_Watchdog_tryWriteMessage___closed__40;
x_258 = x_284;
goto block_278;
}
case 6:
{
lean_object* x_285; 
x_285 = l_Lean_Server_Watchdog_tryWriteMessage___closed__44;
x_258 = x_285;
goto block_278;
}
case 7:
{
lean_object* x_286; 
x_286 = l_Lean_Server_Watchdog_tryWriteMessage___closed__48;
x_258 = x_286;
goto block_278;
}
case 8:
{
lean_object* x_287; 
x_287 = l_Lean_Server_Watchdog_tryWriteMessage___closed__52;
x_258 = x_287;
goto block_278;
}
case 9:
{
lean_object* x_288; 
x_288 = l_Lean_Server_Watchdog_tryWriteMessage___closed__56;
x_258 = x_288;
goto block_278;
}
case 10:
{
lean_object* x_289; 
x_289 = l_Lean_Server_Watchdog_tryWriteMessage___closed__60;
x_258 = x_289;
goto block_278;
}
default: 
{
lean_object* x_290; 
x_290 = l_Lean_Server_Watchdog_tryWriteMessage___closed__64;
x_258 = x_290;
goto block_278;
}
}
block_278:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_259 = l_Lean_Server_Watchdog_tryWriteMessage___closed__15;
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
x_262 = l_List_appendTR___rarg(x_261, x_254);
x_263 = l_Lean_Json_mkObj(x_262);
x_264 = l_Lean_Server_Watchdog_tryWriteMessage___closed__16;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_251);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lean_Json_mkObj(x_269);
x_271 = l_Lean_Json_compress(x_270);
x_272 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1;
x_273 = lean_string_append(x_272, x_271);
lean_dec(x_271);
x_274 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
uint8_t x_297; 
lean_dec(x_3);
x_297 = !lean_is_exclusive(x_5);
if (x_297 == 0)
{
return x_5;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_5, 0);
x_299 = lean_ctor_get(x_5, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_5);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot read LSP notification: ", 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
x_19 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
x_28 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
x_36 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got `shutdown` request, expected an `exit` notification", 55);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
x_7 = lean_string_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1;
x_9 = l_IO_throwServerError___rarg(x_8, x_3);
return x_9;
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1;
x_13 = l_IO_throwServerError___rarg(x_12, x_3);
return x_13;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1;
x_15 = l_IO_throwServerError___rarg(x_14, x_3);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initialized", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1;
lean_inc(x_3);
x_5 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_1);
x_7 = l_Lean_Server_Watchdog_runClientTask(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_Server_Watchdog_mainLoop(x_8, x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_13 = l_IO_FS_Stream_readLspMessage(x_3, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_3(x_12, x_14, x_1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Server_Watchdog_terminateFileWorker___closed__2;
x_19 = lean_apply_3(x_12, x_18, x_1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_Server_Watchdog_shutdown(x_1, x_21);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_20);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_dec(x_5);
x_33 = l_Lean_Server_Watchdog_shutdown(x_1, x_32);
lean_dec(x_1);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_31);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_WORKER_PATH", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_findWorkerPath___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__1;
x_5 = lean_io_getenv(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__2;
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_3(x_8, x_1, x_9, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_apply_3(x_8, x_11, x_12, x_7);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findWorkerPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_SYSROOT", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findWorkerPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_findWorkerPath___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findWorkerPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bin", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_path(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Server_Watchdog_findWorkerPath___closed__1;
x_6 = lean_io_getenv(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_findWorkerPath___closed__2;
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_apply_3(x_9, x_3, x_10, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_Server_Watchdog_findWorkerPath___closed__3;
x_14 = l_System_FilePath_join(x_12, x_13);
x_15 = l_Lean_Server_Watchdog_startFileWorker___closed__9;
x_16 = l_System_FilePath_join(x_14, x_15);
x_17 = l_System_FilePath_exeExtension;
x_18 = l_System_FilePath_withExtension(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_3(x_9, x_18, x_19, x_8);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findWorkerPath___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_findWorkerPath___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findWorkerPath___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_loadReferences___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = l_Lean_Server_Ilean_load(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_References_addIlean(x_4, x_8, x_10);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_8);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_loadReferences(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1;
x_3 = lean_st_ref_get(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2;
x_7 = l_Lean_SearchPath_findAllWithExt(x_4, x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_8);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = l_Lean_Server_References_empty;
x_14 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_loadReferences___spec__1(x_8, x_11, x_12, x_13, x_9);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_loadReferences___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_loadReferences___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("processId", 9);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clientInfo", 10);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rootUri", 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initializationOptions", 21);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("capabilities", 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected param '", 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' for method '", 14);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'\n", 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trace", 5);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspaceFolders", 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC request, got: '", 33);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_13 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2;
x_14 = lean_string_append(x_13, x_3);
lean_dec(x_3);
x_15 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
x_18 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
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
lean_object* x_221; 
x_221 = lean_box(0);
x_22 = x_221;
goto block_220;
}
else
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_11, 0);
lean_inc(x_222);
lean_dec(x_11);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_22 = x_224;
goto block_220;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_22 = x_226;
goto block_220;
}
}
block_220:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__1;
x_24 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_22, x_23);
x_25 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__2;
x_26 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_22, x_25);
x_27 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__3;
x_28 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_22, x_27);
x_29 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__4;
x_30 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(x_22, x_29);
x_31 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__5;
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(x_22, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Json_compress(x_22);
x_35 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__6;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__7;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_3);
lean_dec(x_3);
x_40 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__8;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_33);
lean_dec(x_33);
x_43 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_8)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_8;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
lean_dec(x_32);
x_48 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__9;
x_49 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_22, x_48);
x_50 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__10;
x_51 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(x_22, x_50);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_217; 
lean_dec(x_49);
x_217 = 0;
x_52 = x_217;
goto block_216;
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_49, 0);
lean_inc(x_218);
lean_dec(x_49);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
x_52 = x_219;
goto block_216;
}
block_216:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_53; 
lean_dec(x_24);
x_53 = lean_box(0);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_52);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_54);
if (lean_is_scalar(x_8)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_8;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_47);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_52);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_9);
lean_ctor_set(x_60, 1, x_3);
lean_ctor_set(x_60, 2, x_59);
if (lean_is_scalar(x_8)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_8;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_30, 0);
lean_inc(x_62);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
x_64 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_64, 4, x_47);
lean_ctor_set(x_64, 5, x_53);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_52);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_9);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_64);
if (lean_is_scalar(x_8)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_8;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_7);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_53);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_47);
lean_ctor_set(x_69, 5, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_52);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_69);
if (lean_is_scalar(x_8)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_8;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_7);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_28, 0);
lean_inc(x_72);
lean_dec(x_28);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_51);
x_74 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_74, 0, x_53);
lean_ctor_set(x_74, 1, x_53);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_53);
lean_ctor_set(x_74, 4, x_47);
lean_ctor_set(x_74, 5, x_53);
lean_ctor_set_uint8(x_74, sizeof(void*)*6, x_52);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_9);
lean_ctor_set(x_75, 1, x_3);
lean_ctor_set(x_75, 2, x_74);
if (lean_is_scalar(x_8)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_8;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_7);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_51, 0);
lean_inc(x_77);
lean_dec(x_51);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_79, 0, x_53);
lean_ctor_set(x_79, 1, x_53);
lean_ctor_set(x_79, 2, x_73);
lean_ctor_set(x_79, 3, x_53);
lean_ctor_set(x_79, 4, x_47);
lean_ctor_set(x_79, 5, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*6, x_52);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_9);
lean_ctor_set(x_80, 1, x_3);
lean_ctor_set(x_80, 2, x_79);
if (lean_is_scalar(x_8)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_8;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_7);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_30, 0);
lean_inc(x_82);
lean_dec(x_30);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_51);
x_84 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_53);
lean_ctor_set(x_84, 2, x_73);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_47);
lean_ctor_set(x_84, 5, x_53);
lean_ctor_set_uint8(x_84, sizeof(void*)*6, x_52);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_9);
lean_ctor_set(x_85, 1, x_3);
lean_ctor_set(x_85, 2, x_84);
if (lean_is_scalar(x_8)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_8;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_51, 0);
lean_inc(x_87);
lean_dec(x_51);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_89, 0, x_53);
lean_ctor_set(x_89, 1, x_53);
lean_ctor_set(x_89, 2, x_73);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_47);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*6, x_52);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_9);
lean_ctor_set(x_90, 1, x_3);
lean_ctor_set(x_90, 2, x_89);
if (lean_is_scalar(x_8)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_8;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_7);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_26, 0);
lean_inc(x_92);
lean_dec(x_26);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_51);
x_94 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_94, 0, x_53);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_53);
lean_ctor_set(x_94, 3, x_53);
lean_ctor_set(x_94, 4, x_47);
lean_ctor_set(x_94, 5, x_53);
lean_ctor_set_uint8(x_94, sizeof(void*)*6, x_52);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_9);
lean_ctor_set(x_95, 1, x_3);
lean_ctor_set(x_95, 2, x_94);
if (lean_is_scalar(x_8)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_8;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_51, 0);
lean_inc(x_97);
lean_dec(x_51);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_99, 0, x_53);
lean_ctor_set(x_99, 1, x_93);
lean_ctor_set(x_99, 2, x_53);
lean_ctor_set(x_99, 3, x_53);
lean_ctor_set(x_99, 4, x_47);
lean_ctor_set(x_99, 5, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*6, x_52);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_9);
lean_ctor_set(x_100, 1, x_3);
lean_ctor_set(x_100, 2, x_99);
if (lean_is_scalar(x_8)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_8;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_7);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_30, 0);
lean_inc(x_102);
lean_dec(x_30);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_51);
x_104 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_104, 0, x_53);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_104, 2, x_53);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set(x_104, 4, x_47);
lean_ctor_set(x_104, 5, x_53);
lean_ctor_set_uint8(x_104, sizeof(void*)*6, x_52);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 2, x_104);
if (lean_is_scalar(x_8)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_8;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_7);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_51, 0);
lean_inc(x_107);
lean_dec(x_51);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_109, 0, x_53);
lean_ctor_set(x_109, 1, x_93);
lean_ctor_set(x_109, 2, x_53);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_47);
lean_ctor_set(x_109, 5, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*6, x_52);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_9);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_109);
if (lean_is_scalar(x_8)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_8;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_28, 0);
lean_inc(x_112);
lean_dec(x_28);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_51);
x_114 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_114, 0, x_53);
lean_ctor_set(x_114, 1, x_93);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_53);
lean_ctor_set(x_114, 4, x_47);
lean_ctor_set(x_114, 5, x_53);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_52);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_9);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_114);
if (lean_is_scalar(x_8)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_8;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_51, 0);
lean_inc(x_117);
lean_dec(x_51);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_119, 0, x_53);
lean_ctor_set(x_119, 1, x_93);
lean_ctor_set(x_119, 2, x_113);
lean_ctor_set(x_119, 3, x_53);
lean_ctor_set(x_119, 4, x_47);
lean_ctor_set(x_119, 5, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*6, x_52);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_9);
lean_ctor_set(x_120, 1, x_3);
lean_ctor_set(x_120, 2, x_119);
if (lean_is_scalar(x_8)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_8;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_30, 0);
lean_inc(x_122);
lean_dec(x_30);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_51);
x_124 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_124, 0, x_53);
lean_ctor_set(x_124, 1, x_93);
lean_ctor_set(x_124, 2, x_113);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_47);
lean_ctor_set(x_124, 5, x_53);
lean_ctor_set_uint8(x_124, sizeof(void*)*6, x_52);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_9);
lean_ctor_set(x_125, 1, x_3);
lean_ctor_set(x_125, 2, x_124);
if (lean_is_scalar(x_8)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_8;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_7);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_51, 0);
lean_inc(x_127);
lean_dec(x_51);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_129, 0, x_53);
lean_ctor_set(x_129, 1, x_93);
lean_ctor_set(x_129, 2, x_113);
lean_ctor_set(x_129, 3, x_123);
lean_ctor_set(x_129, 4, x_47);
lean_ctor_set(x_129, 5, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*6, x_52);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_9);
lean_ctor_set(x_130, 1, x_3);
lean_ctor_set(x_130, 2, x_129);
if (lean_is_scalar(x_8)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_8;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_7);
return x_131;
}
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_24, 0);
lean_inc(x_132);
lean_dec(x_24);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_134; 
lean_dec(x_26);
x_134 = lean_box(0);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_51);
x_135 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_47);
lean_ctor_set(x_135, 5, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*6, x_52);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_9);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_135);
if (lean_is_scalar(x_8)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_8;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_7);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_51, 0);
lean_inc(x_138);
lean_dec(x_51);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_140, 2, x_134);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_47);
lean_ctor_set(x_140, 5, x_139);
lean_ctor_set_uint8(x_140, sizeof(void*)*6, x_52);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_9);
lean_ctor_set(x_141, 1, x_3);
lean_ctor_set(x_141, 2, x_140);
if (lean_is_scalar(x_8)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_8;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_7);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_30, 0);
lean_inc(x_143);
lean_dec(x_30);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_51);
x_145 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_145, 0, x_133);
lean_ctor_set(x_145, 1, x_134);
lean_ctor_set(x_145, 2, x_134);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set(x_145, 4, x_47);
lean_ctor_set(x_145, 5, x_134);
lean_ctor_set_uint8(x_145, sizeof(void*)*6, x_52);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_9);
lean_ctor_set(x_146, 1, x_3);
lean_ctor_set(x_146, 2, x_145);
if (lean_is_scalar(x_8)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_8;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_7);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_51, 0);
lean_inc(x_148);
lean_dec(x_51);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_150, 0, x_133);
lean_ctor_set(x_150, 1, x_134);
lean_ctor_set(x_150, 2, x_134);
lean_ctor_set(x_150, 3, x_144);
lean_ctor_set(x_150, 4, x_47);
lean_ctor_set(x_150, 5, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*6, x_52);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_9);
lean_ctor_set(x_151, 1, x_3);
lean_ctor_set(x_151, 2, x_150);
if (lean_is_scalar(x_8)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_8;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_7);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_28, 0);
lean_inc(x_153);
lean_dec(x_28);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_51);
x_155 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_155, 0, x_133);
lean_ctor_set(x_155, 1, x_134);
lean_ctor_set(x_155, 2, x_154);
lean_ctor_set(x_155, 3, x_134);
lean_ctor_set(x_155, 4, x_47);
lean_ctor_set(x_155, 5, x_134);
lean_ctor_set_uint8(x_155, sizeof(void*)*6, x_52);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_9);
lean_ctor_set(x_156, 1, x_3);
lean_ctor_set(x_156, 2, x_155);
if (lean_is_scalar(x_8)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_8;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_7);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_51, 0);
lean_inc(x_158);
lean_dec(x_51);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_160, 0, x_133);
lean_ctor_set(x_160, 1, x_134);
lean_ctor_set(x_160, 2, x_154);
lean_ctor_set(x_160, 3, x_134);
lean_ctor_set(x_160, 4, x_47);
lean_ctor_set(x_160, 5, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*6, x_52);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_9);
lean_ctor_set(x_161, 1, x_3);
lean_ctor_set(x_161, 2, x_160);
if (lean_is_scalar(x_8)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_8;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_7);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_30, 0);
lean_inc(x_163);
lean_dec(x_30);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_51);
x_165 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_165, 0, x_133);
lean_ctor_set(x_165, 1, x_134);
lean_ctor_set(x_165, 2, x_154);
lean_ctor_set(x_165, 3, x_164);
lean_ctor_set(x_165, 4, x_47);
lean_ctor_set(x_165, 5, x_134);
lean_ctor_set_uint8(x_165, sizeof(void*)*6, x_52);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_9);
lean_ctor_set(x_166, 1, x_3);
lean_ctor_set(x_166, 2, x_165);
if (lean_is_scalar(x_8)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_8;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_7);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_51, 0);
lean_inc(x_168);
lean_dec(x_51);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_170, 0, x_133);
lean_ctor_set(x_170, 1, x_134);
lean_ctor_set(x_170, 2, x_154);
lean_ctor_set(x_170, 3, x_164);
lean_ctor_set(x_170, 4, x_47);
lean_ctor_set(x_170, 5, x_169);
lean_ctor_set_uint8(x_170, sizeof(void*)*6, x_52);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_9);
lean_ctor_set(x_171, 1, x_3);
lean_ctor_set(x_171, 2, x_170);
if (lean_is_scalar(x_8)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_8;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_7);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_26, 0);
lean_inc(x_173);
lean_dec(x_26);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_175; 
lean_dec(x_28);
x_175 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_51);
x_176 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_176, 0, x_133);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_175);
lean_ctor_set(x_176, 4, x_47);
lean_ctor_set(x_176, 5, x_175);
lean_ctor_set_uint8(x_176, sizeof(void*)*6, x_52);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_9);
lean_ctor_set(x_177, 1, x_3);
lean_ctor_set(x_177, 2, x_176);
if (lean_is_scalar(x_8)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_8;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_7);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_51, 0);
lean_inc(x_179);
lean_dec(x_51);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_181, 0, x_133);
lean_ctor_set(x_181, 1, x_174);
lean_ctor_set(x_181, 2, x_175);
lean_ctor_set(x_181, 3, x_175);
lean_ctor_set(x_181, 4, x_47);
lean_ctor_set(x_181, 5, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*6, x_52);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_9);
lean_ctor_set(x_182, 1, x_3);
lean_ctor_set(x_182, 2, x_181);
if (lean_is_scalar(x_8)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_8;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_7);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_30, 0);
lean_inc(x_184);
lean_dec(x_30);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_51);
x_186 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_186, 0, x_133);
lean_ctor_set(x_186, 1, x_174);
lean_ctor_set(x_186, 2, x_175);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set(x_186, 4, x_47);
lean_ctor_set(x_186, 5, x_175);
lean_ctor_set_uint8(x_186, sizeof(void*)*6, x_52);
x_187 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_187, 0, x_9);
lean_ctor_set(x_187, 1, x_3);
lean_ctor_set(x_187, 2, x_186);
if (lean_is_scalar(x_8)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_8;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_7);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_51, 0);
lean_inc(x_189);
lean_dec(x_51);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_191, 0, x_133);
lean_ctor_set(x_191, 1, x_174);
lean_ctor_set(x_191, 2, x_175);
lean_ctor_set(x_191, 3, x_185);
lean_ctor_set(x_191, 4, x_47);
lean_ctor_set(x_191, 5, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*6, x_52);
x_192 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_192, 0, x_9);
lean_ctor_set(x_192, 1, x_3);
lean_ctor_set(x_192, 2, x_191);
if (lean_is_scalar(x_8)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_8;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_7);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_28, 0);
lean_inc(x_194);
lean_dec(x_28);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_196; 
lean_dec(x_30);
x_196 = lean_box(0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_51);
x_197 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_197, 0, x_133);
lean_ctor_set(x_197, 1, x_174);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_196);
lean_ctor_set(x_197, 4, x_47);
lean_ctor_set(x_197, 5, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*6, x_52);
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_9);
lean_ctor_set(x_198, 1, x_3);
lean_ctor_set(x_198, 2, x_197);
if (lean_is_scalar(x_8)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_8;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_7);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_51, 0);
lean_inc(x_200);
lean_dec(x_51);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_202, 0, x_133);
lean_ctor_set(x_202, 1, x_174);
lean_ctor_set(x_202, 2, x_195);
lean_ctor_set(x_202, 3, x_196);
lean_ctor_set(x_202, 4, x_47);
lean_ctor_set(x_202, 5, x_201);
lean_ctor_set_uint8(x_202, sizeof(void*)*6, x_52);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_3);
lean_ctor_set(x_203, 2, x_202);
if (lean_is_scalar(x_8)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_8;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_7);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_30, 0);
lean_inc(x_205);
lean_dec(x_30);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_51);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_208, 0, x_133);
lean_ctor_set(x_208, 1, x_174);
lean_ctor_set(x_208, 2, x_195);
lean_ctor_set(x_208, 3, x_206);
lean_ctor_set(x_208, 4, x_47);
lean_ctor_set(x_208, 5, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*6, x_52);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_9);
lean_ctor_set(x_209, 1, x_3);
lean_ctor_set(x_209, 2, x_208);
if (lean_is_scalar(x_8)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_8;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_7);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_51, 0);
lean_inc(x_211);
lean_dec(x_51);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_213, 0, x_133);
lean_ctor_set(x_213, 1, x_174);
lean_ctor_set(x_213, 2, x_195);
lean_ctor_set(x_213, 3, x_206);
lean_ctor_set(x_213, 4, x_47);
lean_ctor_set(x_213, 5, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*6, x_52);
x_214 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_214, 0, x_9);
lean_ctor_set(x_214, 1, x_3);
lean_ctor_set(x_214, 2, x_213);
if (lean_is_scalar(x_8)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_8;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_7);
return x_215;
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
case 1:
{
uint8_t x_227; 
lean_dec(x_3);
x_227 = !lean_is_exclusive(x_5);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_228 = lean_ctor_get(x_5, 0);
lean_dec(x_228);
x_229 = lean_ctor_get(x_6, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_6, 1);
lean_inc(x_230);
lean_dec(x_6);
x_231 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_231, 0, x_229);
x_232 = l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
x_235 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_234, x_230);
lean_dec(x_230);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_Json_mkObj(x_238);
x_240 = l_Lean_Json_compress(x_239);
x_241 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_242 = lean_string_append(x_241, x_240);
lean_dec(x_240);
x_243 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_244 = lean_string_append(x_242, x_243);
x_245 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_245);
return x_5;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_246 = lean_ctor_get(x_5, 1);
lean_inc(x_246);
lean_dec(x_5);
x_247 = lean_ctor_get(x_6, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_6, 1);
lean_inc(x_248);
lean_dec(x_6);
x_249 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_249, 0, x_247);
x_250 = l_Lean_Server_Watchdog_tryWriteMessage___closed__8;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = l_Lean_Server_Watchdog_tryWriteMessage___closed__9;
x_253 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_252, x_248);
lean_dec(x_248);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_Lean_Json_mkObj(x_256);
x_258 = l_Lean_Json_compress(x_257);
x_259 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_260 = lean_string_append(x_259, x_258);
lean_dec(x_258);
x_261 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_262 = lean_string_append(x_260, x_261);
x_263 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_246);
return x_264;
}
}
case 2:
{
uint8_t x_265; 
lean_dec(x_3);
x_265 = !lean_is_exclusive(x_5);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_5, 0);
lean_dec(x_266);
x_267 = lean_ctor_get(x_6, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_6, 1);
lean_inc(x_268);
lean_dec(x_6);
x_269 = l_Lean_Server_Watchdog_tryWriteMessage___closed__12;
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
switch (lean_obj_tag(x_267)) {
case 0:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_273 = lean_ctor_get(x_267, 0);
lean_inc(x_273);
lean_dec(x_267);
x_274 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_272);
x_278 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = l_Lean_Json_mkObj(x_279);
x_281 = l_Lean_Json_compress(x_280);
x_282 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_283 = lean_string_append(x_282, x_281);
lean_dec(x_281);
x_284 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_285 = lean_string_append(x_283, x_284);
x_286 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_286);
return x_5;
}
case 1:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_287 = lean_ctor_get(x_267, 0);
lean_inc(x_287);
lean_dec(x_267);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_272);
x_292 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = l_Lean_Json_mkObj(x_293);
x_295 = l_Lean_Json_compress(x_294);
x_296 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_297 = lean_string_append(x_296, x_295);
lean_dec(x_295);
x_298 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_299 = lean_string_append(x_297, x_298);
x_300 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_300);
return x_5;
}
default: 
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_301 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_272);
x_303 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
x_305 = l_Lean_Json_mkObj(x_304);
x_306 = l_Lean_Json_compress(x_305);
x_307 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_308 = lean_string_append(x_307, x_306);
lean_dec(x_306);
x_309 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_310 = lean_string_append(x_308, x_309);
x_311 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_311);
return x_5;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_5, 1);
lean_inc(x_312);
lean_dec(x_5);
x_313 = lean_ctor_get(x_6, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_6, 1);
lean_inc(x_314);
lean_dec(x_6);
x_315 = l_Lean_Server_Watchdog_tryWriteMessage___closed__12;
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
x_317 = lean_box(0);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
switch (lean_obj_tag(x_313)) {
case 0:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_319 = lean_ctor_get(x_313, 0);
lean_inc(x_319);
lean_dec(x_313);
x_320 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_318);
x_324 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = l_Lean_Json_mkObj(x_325);
x_327 = l_Lean_Json_compress(x_326);
x_328 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_329 = lean_string_append(x_328, x_327);
lean_dec(x_327);
x_330 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_331 = lean_string_append(x_329, x_330);
x_332 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_312);
return x_333;
}
case 1:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_334 = lean_ctor_get(x_313, 0);
lean_inc(x_334);
lean_dec(x_313);
x_335 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_335, 0, x_334);
x_336 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_318);
x_339 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Lean_Json_mkObj(x_340);
x_342 = l_Lean_Json_compress(x_341);
x_343 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_346 = lean_string_append(x_344, x_345);
x_347 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_347, 0, x_346);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_312);
return x_348;
}
default: 
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = l_Lean_Server_Watchdog_tryWriteMessage___closed__11;
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_318);
x_351 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = l_Lean_Json_mkObj(x_352);
x_354 = l_Lean_Json_compress(x_353);
x_355 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_356 = lean_string_append(x_355, x_354);
lean_dec(x_354);
x_357 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_358 = lean_string_append(x_356, x_357);
x_359 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_312);
return x_360;
}
}
}
}
default: 
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_3);
x_361 = lean_ctor_get(x_5, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_362 = x_5;
} else {
 lean_dec_ref(x_5);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_6, 0);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_365 = lean_ctor_get(x_6, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_6, 2);
lean_inc(x_366);
lean_dec(x_6);
x_367 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_367, 0, x_365);
x_368 = l_Lean_Server_Watchdog_tryWriteMessage___closed__13;
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_Lean_Server_Watchdog_tryWriteMessage___closed__14;
x_373 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_372, x_366);
lean_dec(x_366);
switch (lean_obj_tag(x_363)) {
case 0:
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_363, 0);
lean_inc(x_411);
lean_dec(x_363);
x_412 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_374 = x_412;
goto block_410;
}
case 1:
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_363, 0);
lean_inc(x_413);
lean_dec(x_363);
x_414 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_374 = x_414;
goto block_410;
}
default: 
{
lean_object* x_415; 
x_415 = lean_box(0);
x_374 = x_415;
goto block_410;
}
}
block_410:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = l_Lean_Server_Watchdog_tryWriteMessage___closed__10;
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
switch (x_364) {
case 0:
{
lean_object* x_398; 
x_398 = l_Lean_Server_Watchdog_tryWriteMessage___closed__20;
x_377 = x_398;
goto block_397;
}
case 1:
{
lean_object* x_399; 
x_399 = l_Lean_Server_Watchdog_tryWriteMessage___closed__24;
x_377 = x_399;
goto block_397;
}
case 2:
{
lean_object* x_400; 
x_400 = l_Lean_Server_Watchdog_tryWriteMessage___closed__28;
x_377 = x_400;
goto block_397;
}
case 3:
{
lean_object* x_401; 
x_401 = l_Lean_Server_Watchdog_tryWriteMessage___closed__32;
x_377 = x_401;
goto block_397;
}
case 4:
{
lean_object* x_402; 
x_402 = l_Lean_Server_Watchdog_tryWriteMessage___closed__36;
x_377 = x_402;
goto block_397;
}
case 5:
{
lean_object* x_403; 
x_403 = l_Lean_Server_Watchdog_tryWriteMessage___closed__40;
x_377 = x_403;
goto block_397;
}
case 6:
{
lean_object* x_404; 
x_404 = l_Lean_Server_Watchdog_tryWriteMessage___closed__44;
x_377 = x_404;
goto block_397;
}
case 7:
{
lean_object* x_405; 
x_405 = l_Lean_Server_Watchdog_tryWriteMessage___closed__48;
x_377 = x_405;
goto block_397;
}
case 8:
{
lean_object* x_406; 
x_406 = l_Lean_Server_Watchdog_tryWriteMessage___closed__52;
x_377 = x_406;
goto block_397;
}
case 9:
{
lean_object* x_407; 
x_407 = l_Lean_Server_Watchdog_tryWriteMessage___closed__56;
x_377 = x_407;
goto block_397;
}
case 10:
{
lean_object* x_408; 
x_408 = l_Lean_Server_Watchdog_tryWriteMessage___closed__60;
x_377 = x_408;
goto block_397;
}
default: 
{
lean_object* x_409; 
x_409 = l_Lean_Server_Watchdog_tryWriteMessage___closed__64;
x_377 = x_409;
goto block_397;
}
}
block_397:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_378 = l_Lean_Server_Watchdog_tryWriteMessage___closed__15;
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_371);
x_381 = l_List_appendTR___rarg(x_380, x_373);
x_382 = l_Lean_Json_mkObj(x_381);
x_383 = l_Lean_Server_Watchdog_tryWriteMessage___closed__16;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_370);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_376);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_Server_Watchdog_tryWriteMessage___closed__7;
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
x_389 = l_Lean_Json_mkObj(x_388);
x_390 = l_Lean_Json_compress(x_389);
x_391 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11;
x_392 = lean_string_append(x_391, x_390);
lean_dec(x_390);
x_393 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_394 = lean_string_append(x_392, x_393);
x_395 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_395, 0, x_394);
if (lean_is_scalar(x_362)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_362;
 lean_ctor_set_tag(x_396, 1);
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_361);
return x_396;
}
}
}
}
}
else
{
uint8_t x_416; 
lean_dec(x_3);
x_416 = !lean_is_exclusive(x_5);
if (x_416 == 0)
{
return x_5;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_5, 0);
x_418 = lean_ctor_get(x_5, 1);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_5);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot read LSP request: ", 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(x_1, x_5, x_2, x_6);
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
x_11 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
x_19 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
x_28 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
x_36 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_708_(x_5);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(80u);
x_3 = l_Lean_Json_pretty(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1;
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__2;
x_2 = l_Lean_Server_Watchdog_findFileWorker_x21___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__4;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Data_Lsp_Client_0__Lean_Lsp_toJsonRegistrationParams____x40_Lean_Data_Lsp_Client___hyg_172_(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_1, x_9, x_3);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_IO_FS_Stream_writeLspMessage(x_1, x_13, x_3);
lean_dec(x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wdIn.txt", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wdOut.txt", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wdErr.txt", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("0.1.1", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean 4 Server", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__6;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_mainLoop___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("**/*.ilean", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__13;
x_2 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonDidChangeWatchedFilesRegistrationOptions____x40_Lean_Data_Lsp_Workspace___hyg_304_(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__14;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ilean_watcher", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__16;
x_2 = l_Lean_Server_Watchdog_handleNotification___closed__2;
x_3 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__18;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("client/registerCapability", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__10;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__20;
x_3 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Watchdog_findWorkerPath(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_prefix(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_initSrcSearchPath___rarg(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Server_Watchdog_loadReferences(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_mk_ref(x_16, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1;
x_26 = 0;
x_27 = l_Lean_Server_maybeTee(x_25, x_26, x_2, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2;
x_31 = 1;
x_32 = l_Lean_Server_maybeTee(x_30, x_31, x_3, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__3;
x_36 = l_Lean_Server_maybeTee(x_35, x_31, x_4, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Server_Watchdog_startFileWorker___closed__8;
lean_inc(x_28);
x_40 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(x_28, x_39, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__9;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_33);
x_47 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(x_33, x_46, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__21;
lean_inc(x_33);
x_50 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(x_33, x_49, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_44, 3);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(200u);
x_54 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_54, 0, x_28);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_54, 3, x_1);
lean_ctor_set(x_54, 4, x_23);
lean_ctor_set(x_54, 5, x_44);
lean_ctor_set(x_54, 6, x_53);
lean_ctor_set(x_54, 7, x_7);
lean_ctor_set(x_54, 8, x_13);
lean_ctor_set(x_54, 9, x_19);
x_55 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_54, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_unsigned_to_nat(200u);
x_60 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_60, 0, x_28);
lean_ctor_set(x_60, 1, x_33);
lean_ctor_set(x_60, 2, x_37);
lean_ctor_set(x_60, 3, x_1);
lean_ctor_set(x_60, 4, x_23);
lean_ctor_set(x_60, 5, x_44);
lean_ctor_set(x_60, 6, x_59);
lean_ctor_set(x_60, 7, x_7);
lean_ctor_set(x_60, 8, x_13);
lean_ctor_set(x_60, 9, x_19);
x_61 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_60, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_dec(x_50);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_64, 0, x_28);
lean_ctor_set(x_64, 1, x_33);
lean_ctor_set(x_64, 2, x_37);
lean_ctor_set(x_64, 3, x_1);
lean_ctor_set(x_64, 4, x_23);
lean_ctor_set(x_64, 5, x_44);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_64, 7, x_7);
lean_ctor_set(x_64, 8, x_13);
lean_ctor_set(x_64, 9, x_19);
x_65 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_64, x_62);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_50);
if (x_66 == 0)
{
return x_50;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_50, 0);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_50);
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
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_47);
if (x_70 == 0)
{
return x_47;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_40);
if (x_74 == 0)
{
return x_40;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_40, 0);
x_76 = lean_ctor_get(x_40, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_40);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_36);
if (x_78 == 0)
{
return x_36;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_36, 0);
x_80 = lean_ctor_get(x_36, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_36);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
return x_32;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_32, 0);
x_84 = lean_ctor_get(x_32, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_32);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_27);
if (x_86 == 0)
{
return x_27;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_27, 0);
x_88 = lean_ctor_get(x_27, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_27);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_15);
if (x_90 == 0)
{
return x_15;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_15, 0);
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_15);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_12);
if (x_94 == 0)
{
return x_12;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_12, 0);
x_96 = lean_ctor_get(x_12, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_12);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_9);
if (x_98 == 0)
{
return x_9;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_9, 0);
x_100 = lean_ctor_get(x_9, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_9);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_6);
if (x_102 == 0)
{
return x_6;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_6, 0);
x_104 = lean_ctor_get(x_6, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_6);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Watchdog error: ", 16);
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
LEAN_EXPORT lean_object* lean_server_watchdog_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_get_stdin(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
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
x_24 = l_Lean_Server_Watchdog_tryWriteMessage___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_IO_FS_Stream_putStrLn(x_10, x_25, x_20);
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
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_FuzzyMatching(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_References(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Watchdog(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_FuzzyMatching(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Watchdog_workerCfg___closed__1 = _init_l_Lean_Server_Watchdog_workerCfg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_workerCfg___closed__1);
l_Lean_Server_Watchdog_workerCfg = _init_l_Lean_Server_Watchdog_workerCfg();
lean_mark_persistent(l_Lean_Server_Watchdog_workerCfg);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst___closed__1 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst___closed__1();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst___closed__1);
l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1 = _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask_loopAction___closed__1);
l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1 = _init_l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_FileWorker_runEditsSignalTask___closed__1);
l_Lean_Server_Watchdog_findFileWorker_x21___closed__1 = _init_l_Lean_Server_Watchdog_findFileWorker_x21___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_findFileWorker_x21___closed__1);
l_Lean_Server_Watchdog_findFileWorker_x21___closed__2 = _init_l_Lean_Server_Watchdog_findFileWorker_x21___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_findFileWorker_x21___closed__2);
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
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__9);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__10 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__10();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__10);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__11 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__11();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__11);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__12);
l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__2___closed__1);
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
l_Lean_Server_Watchdog_startFileWorker___closed__6 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__6);
l_Lean_Server_Watchdog_startFileWorker___closed__7 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__7);
l_Lean_Server_Watchdog_startFileWorker___closed__8 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__8);
l_Lean_Server_Watchdog_startFileWorker___closed__9 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__9();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__9);
l_Lean_Server_Watchdog_startFileWorker___closed__10 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__10();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__10);
l_Lean_Server_Watchdog_terminateFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_terminateFileWorker___closed__1);
l_Lean_Server_Watchdog_terminateFileWorker___closed__2 = _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_terminateFileWorker___closed__2);
l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__1();
l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___lambda__1___closed__2();
l_Lean_Server_Watchdog_tryWriteMessage___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__2);
l_Lean_Server_Watchdog_tryWriteMessage___closed__3 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__3);
l_Lean_Server_Watchdog_tryWriteMessage___closed__4 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__4);
l_Lean_Server_Watchdog_tryWriteMessage___closed__5 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__5);
l_Lean_Server_Watchdog_tryWriteMessage___closed__6 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__6);
l_Lean_Server_Watchdog_tryWriteMessage___closed__7 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__7);
l_Lean_Server_Watchdog_tryWriteMessage___closed__8 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__8);
l_Lean_Server_Watchdog_tryWriteMessage___closed__9 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__9();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__9);
l_Lean_Server_Watchdog_tryWriteMessage___closed__10 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__10();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__10);
l_Lean_Server_Watchdog_tryWriteMessage___closed__11 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__11();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__11);
l_Lean_Server_Watchdog_tryWriteMessage___closed__12 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__12();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__12);
l_Lean_Server_Watchdog_tryWriteMessage___closed__13 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__13();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__13);
l_Lean_Server_Watchdog_tryWriteMessage___closed__14 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__14();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__14);
l_Lean_Server_Watchdog_tryWriteMessage___closed__15 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__15();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__15);
l_Lean_Server_Watchdog_tryWriteMessage___closed__16 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__16();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__16);
l_Lean_Server_Watchdog_tryWriteMessage___closed__17 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__17();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__17);
l_Lean_Server_Watchdog_tryWriteMessage___closed__18 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__18();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__18);
l_Lean_Server_Watchdog_tryWriteMessage___closed__19 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__19();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__19);
l_Lean_Server_Watchdog_tryWriteMessage___closed__20 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__20();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__20);
l_Lean_Server_Watchdog_tryWriteMessage___closed__21 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__21();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__21);
l_Lean_Server_Watchdog_tryWriteMessage___closed__22 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__22();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__22);
l_Lean_Server_Watchdog_tryWriteMessage___closed__23 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__23();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__23);
l_Lean_Server_Watchdog_tryWriteMessage___closed__24 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__24();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__24);
l_Lean_Server_Watchdog_tryWriteMessage___closed__25 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__25();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__25);
l_Lean_Server_Watchdog_tryWriteMessage___closed__26 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__26();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__26);
l_Lean_Server_Watchdog_tryWriteMessage___closed__27 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__27();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__27);
l_Lean_Server_Watchdog_tryWriteMessage___closed__28 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__28();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__28);
l_Lean_Server_Watchdog_tryWriteMessage___closed__29 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__29();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__29);
l_Lean_Server_Watchdog_tryWriteMessage___closed__30 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__30();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__30);
l_Lean_Server_Watchdog_tryWriteMessage___closed__31 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__31();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__31);
l_Lean_Server_Watchdog_tryWriteMessage___closed__32 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__32();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__32);
l_Lean_Server_Watchdog_tryWriteMessage___closed__33 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__33();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__33);
l_Lean_Server_Watchdog_tryWriteMessage___closed__34 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__34();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__34);
l_Lean_Server_Watchdog_tryWriteMessage___closed__35 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__35();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__35);
l_Lean_Server_Watchdog_tryWriteMessage___closed__36 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__36();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__36);
l_Lean_Server_Watchdog_tryWriteMessage___closed__37 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__37();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__37);
l_Lean_Server_Watchdog_tryWriteMessage___closed__38 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__38();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__38);
l_Lean_Server_Watchdog_tryWriteMessage___closed__39 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__39();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__39);
l_Lean_Server_Watchdog_tryWriteMessage___closed__40 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__40();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__40);
l_Lean_Server_Watchdog_tryWriteMessage___closed__41 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__41();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__41);
l_Lean_Server_Watchdog_tryWriteMessage___closed__42 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__42();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__42);
l_Lean_Server_Watchdog_tryWriteMessage___closed__43 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__43();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__43);
l_Lean_Server_Watchdog_tryWriteMessage___closed__44 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__44();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__44);
l_Lean_Server_Watchdog_tryWriteMessage___closed__45 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__45();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__45);
l_Lean_Server_Watchdog_tryWriteMessage___closed__46 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__46();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__46);
l_Lean_Server_Watchdog_tryWriteMessage___closed__47 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__47();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__47);
l_Lean_Server_Watchdog_tryWriteMessage___closed__48 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__48();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__48);
l_Lean_Server_Watchdog_tryWriteMessage___closed__49 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__49();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__49);
l_Lean_Server_Watchdog_tryWriteMessage___closed__50 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__50();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__50);
l_Lean_Server_Watchdog_tryWriteMessage___closed__51 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__51();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__51);
l_Lean_Server_Watchdog_tryWriteMessage___closed__52 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__52();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__52);
l_Lean_Server_Watchdog_tryWriteMessage___closed__53 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__53();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__53);
l_Lean_Server_Watchdog_tryWriteMessage___closed__54 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__54();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__54);
l_Lean_Server_Watchdog_tryWriteMessage___closed__55 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__55();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__55);
l_Lean_Server_Watchdog_tryWriteMessage___closed__56 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__56();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__56);
l_Lean_Server_Watchdog_tryWriteMessage___closed__57 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__57();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__57);
l_Lean_Server_Watchdog_tryWriteMessage___closed__58 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__58();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__58);
l_Lean_Server_Watchdog_tryWriteMessage___closed__59 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__59();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__59);
l_Lean_Server_Watchdog_tryWriteMessage___closed__60 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__60();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__60);
l_Lean_Server_Watchdog_tryWriteMessage___closed__61 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__61();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__61);
l_Lean_Server_Watchdog_tryWriteMessage___closed__62 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__62();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__62);
l_Lean_Server_Watchdog_tryWriteMessage___closed__63 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__63();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__63);
l_Lean_Server_Watchdog_tryWriteMessage___closed__64 = _init_l_Lean_Server_Watchdog_tryWriteMessage___closed__64();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___closed__64);
l_Lean_Server_Watchdog_findDefinitions___closed__1 = _init_l_Lean_Server_Watchdog_findDefinitions___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_findDefinitions___closed__1);
l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1 = _init_l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Server_Watchdog_handleWorkspaceSymbol___spec__1___closed__1);
l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__1___closed__1();
l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__1 = _init_l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__1);
l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2 = _init_l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleWorkspaceSymbol___lambda__2___closed__2);
l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___lambda__1___closed__1);
l_Lean_Server_Watchdog_handleEdits___closed__1 = _init_l_Lean_Server_Watchdog_handleEdits___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___closed__1);
l_Lean_Server_Watchdog_handleEdits___closed__2 = _init_l_Lean_Server_Watchdog_handleEdits___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___closed__2);
l_Lean_Server_Watchdog_handleEdits___closed__3 = _init_l_Lean_Server_Watchdog_handleEdits___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_handleEdits___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChangeWatchedFiles___spec__3___closed__1);
l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1 = _init_l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__1);
l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2 = _init_l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleDidChangeWatchedFiles___closed__2);
l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1 = _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__1);
l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__2 = _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__2();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___closed__2);
l_Lean_Server_Watchdog_parseParams___rarg___closed__1 = _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_parseParams___rarg___closed__1);
l_Lean_Server_Watchdog_parseParams___rarg___closed__2 = _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_parseParams___rarg___closed__2);
l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_forwardRequestToWorker___lambda__1___closed__1);
l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1 = _init_l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_forwardRequestToWorker___closed__1);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__1);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__2);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__3);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__4);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__5);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__6 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__6);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__7 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__7);
l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8 = _init_l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___lambda__1___closed__8);
l_Lean_Server_Watchdog_handleRequest___closed__1 = _init_l_Lean_Server_Watchdog_handleRequest___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__1);
l_Lean_Server_Watchdog_handleRequest___closed__2 = _init_l_Lean_Server_Watchdog_handleRequest___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__2);
l_Lean_Server_Watchdog_handleNotification___closed__1 = _init_l_Lean_Server_Watchdog_handleNotification___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__1);
l_Lean_Server_Watchdog_handleNotification___closed__2 = _init_l_Lean_Server_Watchdog_handleNotification___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__2);
l_Lean_Server_Watchdog_handleNotification___closed__3 = _init_l_Lean_Server_Watchdog_handleNotification___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__3);
l_Lean_Server_Watchdog_handleNotification___closed__4 = _init_l_Lean_Server_Watchdog_handleNotification___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__4);
l_Lean_Server_Watchdog_handleNotification___closed__5 = _init_l_Lean_Server_Watchdog_handleNotification___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__5);
l_Lean_Server_Watchdog_handleNotification___closed__6 = _init_l_Lean_Server_Watchdog_handleNotification___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__6);
l_Lean_Server_Watchdog_runClientTask___closed__1 = _init_l_Lean_Server_Watchdog_runClientTask___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_runClientTask___closed__1);
l_Lean_Server_Watchdog_runClientTask___closed__2 = _init_l_Lean_Server_Watchdog_runClientTask___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_runClientTask___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_mainLoop___spec__3___closed__1);
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
l_Lean_Server_Watchdog_mainLoop___closed__7 = _init_l_Lean_Server_Watchdog_mainLoop___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__7);
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
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__1);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__2);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___closed__3);
l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1 = _init_l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___lambda__1___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2);
l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__1 = _init_l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__1);
l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__2 = _init_l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_findWorkerPath___lambda__2___closed__2);
l_Lean_Server_Watchdog_findWorkerPath___closed__1 = _init_l_Lean_Server_Watchdog_findWorkerPath___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_findWorkerPath___closed__1);
l_Lean_Server_Watchdog_findWorkerPath___closed__2 = _init_l_Lean_Server_Watchdog_findWorkerPath___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_findWorkerPath___closed__2);
l_Lean_Server_Watchdog_findWorkerPath___closed__3 = _init_l_Lean_Server_Watchdog_findWorkerPath___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_findWorkerPath___closed__3);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__1 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__1);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__2 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__2);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__3 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__3);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__4 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__4);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__5 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__5();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__5);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__6 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__6();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__6);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__7 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__7();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__7);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__8 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__8();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__8);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__9 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__9();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__9);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__10 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__10();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__10);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2___closed__11);
l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1 = _init_l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1___closed__1);
l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__1 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__1();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__1);
l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__2 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__2();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__2);
l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__3 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__3();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__3);
l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__4 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__4();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__5___closed__4);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__3 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__3);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__4 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__4);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__5 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__5);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__6 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__6);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__7 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__7);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__8 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__8);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__9 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__9();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__9);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__10 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__10();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__10);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__11 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__11();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__11);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__12 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__12();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__12);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__13 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__13();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__13);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__14 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__14();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__14);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__15 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__15();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__15);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__16 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__16();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__16);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__17 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__17();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__17);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__18 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__18();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__18);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__19 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__19();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__19);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__20 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__20();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__20);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__21 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__21();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__21);
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

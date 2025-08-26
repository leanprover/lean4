// Lean compiler output
// Module: Lean.Data.Lsp.Ipc
// Imports: Init.System.IO Lean.Data.Json.Basic Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Init.Data.List.Sort.Basic
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
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_DiagnosticWith_fullRange___redArg(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Lsp_Ipc_waitForILeans___closed__1;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58;
static lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedError;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0;
lean_object* l_id___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___closed__0;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*, lean_object*);
uint8_t l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_shutdown___closed__0;
lean_object* l_Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra_2826339401____hygCtx___hyg_33_(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0;
static lean_object* l_Lean_Lsp_Ipc_waitForILeans___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51;
lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__0;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig;
lean_object* l_Lean_Lsp_toJsonWaitForILeansParams____x40_Lean_Data_Lsp_Extra_2963646257____hygCtx___hyg_33_(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22;
lean_object* lean_stream_of_handle(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics_298794665____hygCtx___hyg_70_(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53;
lean_object* l_Lean_Json_opt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__0(lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__1;
uint8_t l_Lean_Lsp_ordRange____x40_Lean_Data_Lsp_BasicAux_2413389941____hygCtx___hyg_75_(lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_fromJson_x3f(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__0(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42;
static lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61;
lean_object* l_List_mergeSort___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_runWith___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
static lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38;
static lean_object* _init_l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_ipcStdioConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_stream_of_handle(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_stream_of_handle(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdin(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_IO_FS_Stream_writeLspRequest___redArg(x_1, x_6, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_writeRequest___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdin(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_IO_FS_Stream_writeLspNotification___redArg(x_1, x_6, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_writeNotification___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_Structured_fromJson_x3f(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_12 = l_Lean_Json_Structured_fromJson_x3f(x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_8 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_8 = x_16;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(0, 3, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_1, x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_11 = l_Lean_Json_Structured_fromJson_x3f(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
x_12 = lean_box(0);
x_7 = x_12;
goto block_10;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
x_7 = x_11;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_7 = x_15;
goto block_10;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_6;
 lean_ctor_set_tag(x_8, 1);
}
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
return x_9;
}
}
}
static lean_object* _init_l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instInhabitedError;
x_2 = l_EStateM_instInhabited___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___closed__0;
x_5 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_2(x_6, x_2, x_3);
return x_7;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exit", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.Lsp.Ipc", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Lsp.Ipc.shutdown", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: result.isNull\n      ", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(56u);
x_4 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__2;
x_5 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected id ", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", got id ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l_IO_FS_Stream_readLspMessage(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = l_Lean_Json_isNull(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_12);
x_24 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4;
lean_inc_ref(x_7);
x_25 = l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(x_24, x_7, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec_ref(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec_ref(x_26);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec_ref(x_25);
x_8 = x_33;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_39 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_21, x_5);
if (x_39 == 0)
{
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_6);
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_40 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5;
x_41 = l_Nat_reprFast(x_6);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6;
x_44 = lean_string_append(x_42, x_43);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_21);
x_51 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
x_52 = lean_string_append(x_51, x_50);
lean_dec_ref(x_50);
x_53 = lean_string_append(x_52, x_51);
x_45 = x_53;
goto block_49;
}
case 1:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_21);
x_55 = l_Lean_JsonNumber_toString(x_54);
x_45 = x_55;
goto block_49;
}
default: 
{
lean_object* x_56; 
x_56 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
x_45 = x_56;
goto block_49;
}
}
block_49:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = lean_mk_io_user_error(x_46);
if (lean_is_scalar(x_12)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_12;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_11);
return x_48;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_6);
goto block_20;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_10);
x_8 = x_11;
goto _start;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(x_3, x_14, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
return x_15;
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_1);
x_9 = l_IO_FS_Stream_readLspMessage(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = l_Lean_Json_isNull(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_12);
x_24 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4;
lean_inc_ref(x_7);
x_25 = l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3(x_24, x_7, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec_ref(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_26);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec_ref(x_25);
x_34 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_39 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_21, x_5);
if (x_39 == 0)
{
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_6);
goto block_20;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_40 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5;
x_41 = l_Nat_reprFast(x_6);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6;
x_44 = lean_string_append(x_42, x_43);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_21);
x_51 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
x_52 = lean_string_append(x_51, x_50);
lean_dec_ref(x_50);
x_53 = lean_string_append(x_52, x_51);
x_45 = x_53;
goto block_49;
}
case 1:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_54);
lean_dec_ref(x_21);
x_55 = l_Lean_JsonNumber_toString(x_54);
x_45 = x_55;
goto block_49;
}
default: 
{
lean_object* x_56; 
x_56 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
x_45 = x_56;
goto block_49;
}
}
block_49:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_string_append(x_44, x_45);
lean_dec_ref(x_45);
x_47 = lean_mk_io_user_error(x_46);
if (lean_is_scalar(x_12)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_12;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_11);
return x_48;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_6);
goto block_20;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_12);
lean_dec(x_10);
x_57 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_57;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_IO_FS_Stream_writeLspNotification___at___Lean_Lsp_Ipc_shutdown_spec__2(x_3, x_14, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
return x_15;
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_shutdown___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shutdown", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_2);
x_4 = l_Lean_Lsp_Ipc_stdout(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
lean_inc_ref(x_2);
x_7 = l_Lean_Lsp_Ipc_stdin(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_1);
x_10 = l_Lean_JsonNumber_fromNat(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Lsp_Ipc_shutdown___closed__0;
x_13 = lean_box(0);
lean_inc_ref(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_inc(x_8);
x_15 = l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_shutdown_spec__0(x_8, x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_box(0);
x_18 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(x_5, x_13, x_8, x_17, x_11, x_1, x_2, x_16);
lean_dec_ref(x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
return x_18;
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Lsp_Ipc_stdout(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_IO_FS_Stream_readLspMessage(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdout(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_IO_FS_Stream_readLspRequestAs___redArg(x_6, x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_readRequestAs___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected result '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected JSON-RPC response, got: '", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("jsonrpc", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("2.0", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6;
x_2 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("message", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("id", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59;
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_3);
x_5 = l_Lean_Lsp_Ipc_stdout(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
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
x_9 = l_IO_FS_Stream_readLspMessage(x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
switch (lean_obj_tag(x_10)) {
case 2:
{
uint8_t x_19; 
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_20, x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_10);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_2);
x_23 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_1);
x_37 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
x_38 = lean_string_append(x_37, x_36);
lean_dec_ref(x_36);
x_39 = lean_string_append(x_38, x_37);
x_24 = x_39;
goto block_35;
}
case 1:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = l_Lean_JsonNumber_toString(x_40);
x_24 = x_41;
goto block_35;
}
default: 
{
lean_object* x_42; 
x_42 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
x_24 = x_42;
goto block_35;
}
}
block_35:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6;
x_27 = lean_string_append(x_25, x_26);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_20);
x_29 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
x_30 = lean_string_append(x_29, x_28);
lean_dec_ref(x_28);
x_31 = lean_string_append(x_30, x_29);
x_13 = x_27;
x_14 = x_31;
goto block_18;
}
case 1:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_20);
x_33 = l_Lean_JsonNumber_toString(x_32);
x_13 = x_27;
x_14 = x_33;
goto block_18;
}
default: 
{
lean_object* x_34; 
x_34 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
x_13 = x_27;
x_14 = x_34;
goto block_18;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_20);
lean_dec(x_12);
lean_inc(x_21);
x_43 = lean_apply_1(x_2, x_21);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_10);
lean_dec(x_1);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0;
x_46 = l_Lean_Json_compress(x_21);
x_47 = lean_string_append(x_45, x_46);
lean_dec_ref(x_46);
x_48 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_string_append(x_49, x_44);
lean_dec(x_44);
x_51 = lean_mk_io_user_error(x_50);
if (lean_is_scalar(x_8)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_8;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_11);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_21);
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
lean_dec_ref(x_43);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_53);
lean_ctor_set(x_10, 0, x_1);
if (lean_is_scalar(x_8)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_8;
}
lean_ctor_set(x_54, 0, x_10);
lean_ctor_set(x_54, 1, x_11);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_10, 0);
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_10);
x_57 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_55, x_1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_2);
x_58 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5;
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_71);
lean_dec_ref(x_1);
x_72 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
x_73 = lean_string_append(x_72, x_71);
lean_dec_ref(x_71);
x_74 = lean_string_append(x_73, x_72);
x_59 = x_74;
goto block_70;
}
case 1:
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_75);
lean_dec_ref(x_1);
x_76 = l_Lean_JsonNumber_toString(x_75);
x_59 = x_76;
goto block_70;
}
default: 
{
lean_object* x_77; 
x_77 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
x_59 = x_77;
goto block_70;
}
}
block_70:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_string_append(x_58, x_59);
lean_dec_ref(x_59);
x_61 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6;
x_62 = lean_string_append(x_60, x_61);
switch (lean_obj_tag(x_55)) {
case 0:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_63);
lean_dec_ref(x_55);
x_64 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7;
x_65 = lean_string_append(x_64, x_63);
lean_dec_ref(x_63);
x_66 = lean_string_append(x_65, x_64);
x_13 = x_62;
x_14 = x_66;
goto block_18;
}
case 1:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_67);
lean_dec_ref(x_55);
x_68 = l_Lean_JsonNumber_toString(x_67);
x_13 = x_62;
x_14 = x_68;
goto block_18;
}
default: 
{
lean_object* x_69; 
x_69 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8;
x_13 = x_62;
x_14 = x_69;
goto block_18;
}
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_55);
lean_dec(x_12);
lean_inc(x_56);
x_78 = lean_apply_1(x_2, x_56);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0;
x_81 = l_Lean_Json_compress(x_56);
x_82 = lean_string_append(x_80, x_81);
lean_dec_ref(x_81);
x_83 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_string_append(x_84, x_79);
lean_dec(x_79);
x_86 = lean_mk_io_user_error(x_85);
if (lean_is_scalar(x_8)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_8;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_11);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_56);
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
lean_dec_ref(x_78);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_8)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_8;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_11);
return x_90;
}
}
}
}
case 3:
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_125; lean_object* x_126; 
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_10, 0);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_93 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_10, 2);
lean_inc(x_94);
lean_dec_ref(x_10);
x_95 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2;
x_96 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3;
x_97 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7;
x_125 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11;
switch (lean_obj_tag(x_91)) {
case 0:
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_91);
if (x_143 == 0)
{
lean_ctor_set_tag(x_91, 3);
x_126 = x_91;
goto block_142;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_91, 0);
lean_inc(x_144);
lean_dec(x_91);
x_145 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_126 = x_145;
goto block_142;
}
}
case 1:
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_91);
if (x_146 == 0)
{
lean_ctor_set_tag(x_91, 2);
x_126 = x_91;
goto block_142;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_91, 0);
lean_inc(x_147);
lean_dec(x_91);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_126 = x_148;
goto block_142;
}
}
default: 
{
lean_object* x_149; 
x_149 = lean_box(0);
x_126 = x_149;
goto block_142;
}
}
block_124:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8;
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_93);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9;
x_110 = l_Lean_Json_opt___redArg(x_96, x_109, x_94);
x_111 = l_List_appendTR___redArg(x_108, x_110);
x_112 = l_Lean_Json_mkObj(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_97);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Json_mkObj(x_116);
x_118 = l_Lean_Json_compress(x_117);
x_119 = lean_string_append(x_95, x_118);
lean_dec_ref(x_118);
x_120 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_mk_io_user_error(x_121);
if (lean_is_scalar(x_8)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_8;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_11);
return x_123;
}
block_142:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12;
x_129 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13;
switch (x_92) {
case 0:
{
lean_object* x_130; 
x_130 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_130;
goto block_124;
}
case 1:
{
lean_object* x_131; 
x_131 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_131;
goto block_124;
}
case 2:
{
lean_object* x_132; 
x_132 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_132;
goto block_124;
}
case 3:
{
lean_object* x_133; 
x_133 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_133;
goto block_124;
}
case 4:
{
lean_object* x_134; 
x_134 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_134;
goto block_124;
}
case 5:
{
lean_object* x_135; 
x_135 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_135;
goto block_124;
}
case 6:
{
lean_object* x_136; 
x_136 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_136;
goto block_124;
}
case 7:
{
lean_object* x_137; 
x_137 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_137;
goto block_124;
}
case 8:
{
lean_object* x_138; 
x_138 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_138;
goto block_124;
}
case 9:
{
lean_object* x_139; 
x_139 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_139;
goto block_124;
}
case 10:
{
lean_object* x_140; 
x_140 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_140;
goto block_124;
}
default: 
{
lean_object* x_141; 
x_141 = l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61;
x_98 = x_128;
x_99 = x_129;
x_100 = x_127;
x_101 = x_141;
goto block_124;
}
}
}
}
default: 
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = lean_mk_io_user_error(x_15);
if (lean_is_scalar(x_12)) {
 x_17 = lean_alloc_ctor(1, 2, 0);
} else {
 x_17 = x_12;
 lean_ctor_set_tag(x_17, 1);
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
uint8_t x_151; 
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_9);
if (x_151 == 0)
{
return x_9;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_9, 0);
x_153 = lean_ctor_get(x_9, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_9);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_readResponseAs___redArg(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_4 = lean_io_process_child_wait(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_Ipc_waitForExit(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(x_1);
x_8 = l_Lean_Lsp_DiagnosticWith_fullRange___redArg(x_2);
x_9 = l_Lean_Lsp_ordRange____x40_Lean_Data_Lsp_BasicAux_2413389941____hygCtx___hyg_75_(x_7, x_8);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
if (x_9 == 1)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 6);
x_11 = lean_ctor_get(x_2, 6);
x_12 = lean_string_dec_lt(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_string_dec_eq(x_10, x_11);
if (x_13 == 0)
{
return x_13;
}
else
{
x_3 = x_9;
goto block_6;
}
}
else
{
return x_12;
}
}
else
{
x_3 = x_9;
goto block_6;
}
block_6:
{
if (x_3 == 2)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed), 2, 0);
x_5 = lean_array_to_list(x_3);
x_6 = l_List_mergeSort___redArg(x_5, x_4);
x_7 = lean_array_mk(x_6);
lean_ctor_set(x_1, 2, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed), 2, 0);
x_12 = lean_array_to_list(x_10);
x_13 = l_List_mergeSort___redArg(x_12, x_11);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot decode publishDiagnostics parameters\n", 44, 44);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Waiting for diagnostics failed: ", 32, 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_2);
x_4 = l_Lean_Lsp_Ipc_readMessage(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; 
lean_dec_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_3 = x_6;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0;
x_15 = lean_string_dec_eq(x_12, x_14);
lean_dec_ref(x_12);
if (x_15 == 0)
{
lean_free_object(x_5);
lean_dec(x_13);
lean_free_object(x_4);
x_3 = x_9;
goto _start;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_free_object(x_5);
lean_free_object(x_4);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_19 = x_13;
} else {
 lean_dec_ref(x_13);
 x_19 = lean_box(0);
}
x_20 = l_Lean_Json_Structured_toJson(x_18);
x_21 = l_Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics_298794665____hygCtx___hyg_70_(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_free_object(x_5);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_mk_io_user_error(x_24);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_4);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec_ref(x_21);
x_27 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(x_26);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_14);
x_31 = x_5;
goto block_34;
}
else
{
lean_object* x_36; 
lean_dec(x_26);
lean_free_object(x_5);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec_ref(x_28);
x_31 = x_36;
goto block_34;
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
if (lean_is_scalar(x_19)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_19;
}
lean_ctor_set(x_32, 0, x_31);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_dec(x_26);
lean_dec(x_19);
lean_free_object(x_5);
return x_27;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_5, 0);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_5);
x_39 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0;
x_40 = lean_string_dec_eq(x_37, x_39);
lean_dec_ref(x_37);
if (x_40 == 0)
{
lean_dec(x_38);
lean_free_object(x_4);
x_3 = x_9;
goto _start;
}
else
{
if (lean_obj_tag(x_38) == 0)
{
lean_free_object(x_4);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Json_Structured_toJson(x_43);
x_46 = l_Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics_298794665____hygCtx___hyg_70_(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = lean_mk_io_user_error(x_49);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_50);
return x_4;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_4);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec_ref(x_46);
x_52 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_39);
lean_ctor_set(x_61, 1, x_60);
x_56 = x_61;
goto block_59;
}
else
{
lean_object* x_62; 
lean_dec(x_51);
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
lean_dec_ref(x_53);
x_56 = x_62;
goto block_59;
}
block_59:
{
lean_object* x_57; lean_object* x_58; 
if (lean_is_scalar(x_44)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_44;
}
lean_ctor_set(x_57, 0, x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
lean_dec(x_51);
lean_dec(x_44);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
lean_dec(x_4);
x_64 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_5, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_66 = x_5;
} else {
 lean_dec_ref(x_5);
 x_66 = lean_box(0);
}
x_67 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0;
x_68 = lean_string_dec_eq(x_64, x_67);
lean_dec_ref(x_64);
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
x_3 = x_63;
goto _start;
}
else
{
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_66);
x_3 = x_63;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Json_Structured_toJson(x_71);
x_74 = l_Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics_298794665____hygCtx___hyg_70_(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_72);
lean_dec(x_66);
lean_dec_ref(x_2);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
x_78 = lean_mk_io_user_error(x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_63);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
lean_dec_ref(x_74);
x_81 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_63);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Lean_Lsp_Ipc_normalizePublishDiagnosticsParams(x_80);
if (lean_is_scalar(x_66)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_66;
 lean_ctor_set_tag(x_90, 0);
}
lean_ctor_set(x_90, 0, x_67);
lean_ctor_set(x_90, 1, x_89);
x_85 = x_90;
goto block_88;
}
else
{
lean_object* x_91; 
lean_dec(x_80);
lean_dec(x_66);
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
lean_dec_ref(x_82);
x_85 = x_91;
goto block_88;
}
block_88:
{
lean_object* x_86; lean_object* x_87; 
if (lean_is_scalar(x_72)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_72;
}
lean_ctor_set(x_86, 0, x_85);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
else
{
lean_dec(x_80);
lean_dec(x_72);
lean_dec(x_66);
return x_81;
}
}
}
}
}
}
case 2:
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_4);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_4, 1);
x_94 = lean_ctor_get(x_4, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_5, 0);
lean_inc(x_95);
lean_dec_ref(x_5);
x_96 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_95, x_1);
lean_dec(x_95);
if (x_96 == 0)
{
lean_free_object(x_4);
x_3 = x_93;
goto _start;
}
else
{
lean_object* x_98; 
lean_dec_ref(x_2);
x_98 = lean_box(0);
lean_ctor_set(x_4, 0, x_98);
return x_4;
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_4, 1);
lean_inc(x_99);
lean_dec(x_4);
x_100 = lean_ctor_get(x_5, 0);
lean_inc(x_100);
lean_dec_ref(x_5);
x_101 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_100, x_1);
lean_dec(x_100);
if (x_101 == 0)
{
x_3 = x_99;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_2);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
return x_104;
}
}
}
default: 
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_4);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_4, 1);
x_107 = lean_ctor_get(x_4, 0);
lean_dec(x_107);
x_108 = lean_ctor_get(x_5, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_109);
lean_dec_ref(x_5);
x_110 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_108, x_1);
lean_dec(x_108);
if (x_110 == 0)
{
lean_dec_ref(x_109);
lean_free_object(x_4);
x_3 = x_106;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_2);
x_112 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_113 = lean_string_append(x_112, x_109);
lean_dec_ref(x_109);
x_114 = lean_mk_io_user_error(x_113);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_114);
return x_4;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_4, 1);
lean_inc(x_115);
lean_dec(x_4);
x_116 = lean_ctor_get(x_5, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_117);
lean_dec_ref(x_5);
x_118 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_116, x_1);
lean_dec(x_116);
if (x_118 == 0)
{
lean_dec_ref(x_117);
x_3 = x_115;
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_2);
x_120 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_121 = lean_string_append(x_120, x_117);
lean_dec_ref(x_117);
x_122 = lean_mk_io_user_error(x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
return x_123;
}
}
}
}
}
else
{
uint8_t x_124; 
lean_dec_ref(x_2);
x_124 = !lean_is_exclusive(x_4);
if (x_124 == 0)
{
return x_4;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_4, 0);
x_126 = lean_ctor_get(x_4, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_4);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra_2826339401____hygCtx___hyg_33_(x_1);
x_3 = l_Lean_Json_Structured_fromJson_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_12 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0_spec__0(x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_8 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_8 = x_16;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(0, 3, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_1, x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Lsp_Ipc_stdin(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0_spec__0(x_5, x_1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("textDocument/waitForDiagnostics", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__0;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_inc_ref(x_4);
x_9 = l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_collectDiagnostics_spec__0(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_4, x_10);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_toJsonWaitForILeansParams____x40_Lean_Data_Lsp_Extra_2963646257____hygCtx___hyg_33_(x_1);
x_3 = l_Lean_Json_Structured_fromJson_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_12 = l_Lean_Json_toStructured_x3f___at___IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0_spec__0(x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_8 = x_13;
goto block_11;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
x_8 = x_12;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_8 = x_16;
goto block_11;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
if (lean_is_scalar(x_7)) {
 x_9 = lean_alloc_ctor(0, 3, 0);
} else {
 x_9 = x_7;
}
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_1, x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Lsp_Ipc_stdin(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_IO_FS_Stream_writeLspRequest___at___Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0_spec__0(x_5, x_1, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Waiting for ILeans failed: ", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_4);
x_6 = l_Lean_Lsp_Ipc_readMessage(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 2:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_12, x_1);
lean_dec(x_12);
if (x_14 == 0)
{
lean_free_object(x_7);
lean_free_object(x_6);
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_16);
return x_6;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_free_object(x_6);
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_4);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_24 = x_7;
} else {
 lean_dec_ref(x_7);
 x_24 = lean_box(0);
}
x_25 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_23, x_1);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_24);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_3);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
 lean_ctor_set_tag(x_28, 0);
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
case 3:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_7);
x_35 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_33, x_1);
lean_dec(x_33);
if (x_35 == 0)
{
lean_dec_ref(x_34);
lean_free_object(x_6);
x_5 = x_31;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_4);
x_37 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0;
x_38 = lean_string_append(x_37, x_34);
lean_dec_ref(x_34);
x_39 = lean_mk_io_user_error(x_38);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_39);
return x_6;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_7);
x_43 = l_Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc_1001020224____hygCtx___hyg_30_(x_41, x_1);
lean_dec(x_41);
if (x_43 == 0)
{
lean_dec_ref(x_42);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_4);
x_45 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0;
x_46 = lean_string_append(x_45, x_42);
lean_dec_ref(x_42);
x_47 = lean_mk_io_user_error(x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
}
default: 
{
lean_object* x_49; 
lean_dec(x_7);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec_ref(x_6);
x_5 = x_49;
goto _start;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_4);
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
return x_6;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_waitForILeans___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("$/lean/waitForILeans", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_waitForILeans___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForILeans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Lsp_Ipc_waitForILeans___closed__0;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_inc_ref(x_4);
x_9 = l_Lean_Lsp_Ipc_writeRequest___at___Lean_Lsp_Ipc_waitForILeans_spec__0(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Lsp_Ipc_waitForILeans___closed__1;
x_13 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(x_1, x_12, x_11, x_4, x_10);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec_ref(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec_ref(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_string_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
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
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc_ref(x_2);
x_4 = l_Lean_Lsp_Ipc_readMessage(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0;
x_12 = lean_string_dec_eq(x_9, x_11);
lean_dec_ref(x_9);
if (x_12 == 0)
{
lean_dec(x_10);
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
if (lean_obj_tag(x_10) == 0)
{
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec_ref(x_10);
x_16 = l_Lean_Json_Structured_toJson(x_15);
x_17 = l_Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics_298794665____hygCtx___hyg_70_(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = lean_mk_io_user_error(x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec_ref(x_23);
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec_ref(x_23);
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_31 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(x_1, x_23, x_29, x_30);
lean_dec_ref(x_23);
if (x_31 == 0)
{
lean_free_object(x_4);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_33; 
lean_dec_ref(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
}
}
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec_ref(x_5);
x_37 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0;
x_38 = lean_string_dec_eq(x_35, x_37);
lean_dec_ref(x_35);
if (x_38 == 0)
{
lean_dec(x_36);
x_3 = x_34;
goto _start;
}
else
{
if (lean_obj_tag(x_36) == 0)
{
x_3 = x_34;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec_ref(x_36);
x_42 = l_Lean_Json_Structured_toJson(x_41);
x_43 = l_Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics_298794665____hygCtx___hyg_70_(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_2);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = lean_mk_io_user_error(x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_34);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec_ref(x_43);
x_50 = lean_ctor_get(x_49, 2);
lean_inc_ref(x_50);
lean_dec(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_array_get_size(x_50);
x_53 = lean_nat_dec_lt(x_51, x_52);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec_ref(x_50);
x_3 = x_34;
goto _start;
}
else
{
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec_ref(x_50);
x_3 = x_34;
goto _start;
}
else
{
size_t x_56; size_t x_57; uint8_t x_58; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_58 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(x_1, x_50, x_56, x_57);
lean_dec_ref(x_50);
if (x_58 == 0)
{
x_3 = x_34;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_2);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_34);
return x_61;
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
lean_object* x_62; 
lean_dec(x_5);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
lean_dec_ref(x_4);
x_3 = x_62;
goto _start;
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
return x_4;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_4);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_waitForMessage_loop(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_waitForMessage(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_runWith___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_6 = lean_box(0);
x_7 = l_Lean_Lsp_Ipc_runWith___redArg___closed__0;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = lean_io_process_spawn(x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_apply_2(x_3, x_12, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Lsp_Ipc_runWith___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Ipc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0 = _init_l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig___closed__0);
l_Lean_Lsp_Ipc_ipcStdioConfig = _init_l_Lean_Lsp_Ipc_ipcStdioConfig();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig);
l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___closed__0 = _init_l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___closed__0();
lean_mark_persistent(l_panic___at___Lean_Lsp_Ipc_shutdown_spec__3___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__2 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__2();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__2);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__3 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__3();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__3);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__4);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__5);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__6);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__7);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_shutdown_spec__4_spec__4___redArg___closed__8);
l_Lean_Lsp_Ipc_shutdown___closed__0 = _init_l_Lean_Lsp_Ipc_shutdown___closed__0();
lean_mark_persistent(l_Lean_Lsp_Ipc_shutdown___closed__0);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__0);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__1);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__2);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__3);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__4);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__5);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__6);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__7);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__8);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__9);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__10);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__11);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__12);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__13);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__14);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__15);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__16);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__17);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__18);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__19);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__20);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__21);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__22);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__23);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__24);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__25);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__26);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__27);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__28);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__29);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__30);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__31);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__32);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__33);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__34);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__35);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__36);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__37);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__38);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__39);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__40);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__41);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__42);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__43);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__44);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__45);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__46);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__47);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__48);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__49);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__50);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__51);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__52);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__53);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__54);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__55);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__56);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__57);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__58);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__59);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__60);
l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61 = _init_l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___redArg___closed__61);
l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0 = _init_l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0();
lean_mark_persistent(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__0);
l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1 = _init_l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1);
l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2 = _init_l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Ipc_0__Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2);
l_Lean_Lsp_Ipc_collectDiagnostics___closed__0 = _init_l_Lean_Lsp_Ipc_collectDiagnostics___closed__0();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics___closed__0);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Lsp_Ipc_waitForILeans_spec__3___redArg___closed__0);
l_Lean_Lsp_Ipc_waitForILeans___closed__0 = _init_l_Lean_Lsp_Ipc_waitForILeans___closed__0();
lean_mark_persistent(l_Lean_Lsp_Ipc_waitForILeans___closed__0);
l_Lean_Lsp_Ipc_waitForILeans___closed__1 = _init_l_Lean_Lsp_Ipc_waitForILeans___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_waitForILeans___closed__1);
l_Lean_Lsp_Ipc_runWith___redArg___closed__0 = _init_l_Lean_Lsp_Ipc_runWith___redArg___closed__0();
lean_mark_persistent(l_Lean_Lsp_Ipc_runWith___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

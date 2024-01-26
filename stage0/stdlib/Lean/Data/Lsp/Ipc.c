// Lean compiler output
// Module: Lean.Data.Lsp.Ipc
// Imports: Init Init.System.IO Lean.Data.Json Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra
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
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__53;
static lean_object* l_Lean_Lsp_Ipc_runWith___rarg___closed__1;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__58;
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__27;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*);
static lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__60;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__41;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__50;
static lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__22;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__44;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__18;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__45;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__25;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__52;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__20;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7;
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__8;
lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__46;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__17;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__5;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2;
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__2;
lean_object* l_EStateM_instInhabitedEStateM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__31;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__63;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__34;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__32;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__30;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__61;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__4;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__26;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__36;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__14;
lean_object* lean_stream_of_handle(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__39;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_445_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Lsp_Ipc_shutdown___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__15;
extern lean_object* l_IO_instInhabitedError;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__6;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__16;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__28;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__43;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__62;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__24;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_shutdown___closed__1;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__21;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__48;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__35;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__7;
LEAN_EXPORT lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__23;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__59;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_shutdown___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__9;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__56;
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__55;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__49;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__19;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__33;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__13;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__38;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__51;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1783_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__47;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__11;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__10;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__40;
static lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__54;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__12;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__57;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__42;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__3;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__29;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__37;
static lean_object* _init_l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1() {
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
static lean_object* _init_l_Lean_Lsp_Ipc_ipcStdioConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
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
lean_dec(x_1);
x_4 = lean_stream_of_handle(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdin(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_Stream_writeLspRequest___rarg(x_1, x_6, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_writeRequest___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Lsp_Ipc_stdin(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_FS_Stream_writeLspNotification___rarg(x_1, x_6, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_writeNotification___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected structured object, got '", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2(lean_object* x_1) {
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
x_10 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_shutdown___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2(x_6);
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
static lean_object* _init_l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_instInhabitedError;
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabitedEStateM___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2;
x_5 = lean_panic_fn(x_4, x_1);
x_6 = lean_apply_2(x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Lsp_Ipc_shutdown___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_IO_FS_Stream_writeLspMessage(x_1, x_12, x_3);
lean_dec(x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2;
x_6 = l_IO_FS_Stream_writeLspNotification___at_Lean_Lsp_Ipc_shutdown___spec__4(x_1, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3;
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result.isNull\n      ", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2;
x_2 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Data.Lsp.Ipc", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Lsp.Ipc.shutdown", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5;
x_2 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6;
x_3 = lean_unsigned_to_nat(50u);
x_4 = lean_unsigned_to_nat(6u);
x_5 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected id ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", got id ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\"", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_15; 
lean_dec(x_5);
lean_inc(x_2);
x_15 = l_IO_FS_Stream_readLspMessage(x_2, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 2)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_Json_isNull(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_free_object(x_15);
x_23 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7;
lean_inc(x_6);
x_24 = l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3(x_23, x_6, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_8 = x_25;
x_9 = x_26;
goto block_14;
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_20, x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_32 = l_Nat_repr(x_1);
x_33 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
x_34 = lean_string_append(x_33, x_32);
lean_dec(x_32);
x_35 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
x_36 = lean_string_append(x_34, x_35);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
lean_dec(x_20);
x_38 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = lean_string_append(x_39, x_38);
x_41 = lean_string_append(x_36, x_40);
lean_dec(x_40);
x_42 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_44);
return x_15;
}
case 1:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_20, 0);
lean_inc(x_45);
lean_dec(x_20);
x_46 = l_Lean_JsonNumber_toString(x_45);
x_47 = lean_string_append(x_36, x_46);
lean_dec(x_46);
x_48 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_50);
return x_15;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_52 = lean_string_append(x_36, x_51);
x_53 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_55);
return x_15;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_20);
lean_free_object(x_15);
x_56 = lean_box(0);
lean_inc(x_3);
x_57 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1(x_3, x_56, x_6, x_18);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_8 = x_58;
x_9 = x_59;
goto block_14;
}
else
{
uint8_t x_60; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_15, 1);
lean_inc(x_64);
lean_dec(x_15);
x_65 = lean_ctor_get(x_16, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_dec(x_16);
x_67 = l_Lean_Json_isNull(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_65);
x_68 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7;
lean_inc(x_6);
x_69 = l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3(x_68, x_6, x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_8 = x_70;
x_9 = x_71;
goto block_14;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_65, x_4);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_77 = l_Nat_repr(x_1);
x_78 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
x_81 = lean_string_append(x_79, x_80);
switch (lean_obj_tag(x_65)) {
case 0:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_65, 0);
lean_inc(x_82);
lean_dec(x_65);
x_83 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = lean_string_append(x_84, x_83);
x_86 = lean_string_append(x_81, x_85);
lean_dec(x_85);
x_87 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_64);
return x_90;
}
case 1:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_65, 0);
lean_inc(x_91);
lean_dec(x_65);
x_92 = l_Lean_JsonNumber_toString(x_91);
x_93 = lean_string_append(x_81, x_92);
lean_dec(x_92);
x_94 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_64);
return x_97;
}
default: 
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_99 = lean_string_append(x_81, x_98);
x_100 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_64);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_65);
x_104 = lean_box(0);
lean_inc(x_3);
x_105 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1(x_3, x_104, x_6, x_64);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_8 = x_106;
x_9 = x_107;
goto block_14;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_105, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_110 = x_105;
} else {
 lean_dec_ref(x_105);
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
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_16);
x_112 = lean_ctor_get(x_15, 1);
lean_inc(x_112);
lean_dec(x_15);
x_113 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1;
x_8 = x_113;
x_9 = x_112;
goto block_14;
}
}
else
{
uint8_t x_114; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_15);
if (x_114 == 0)
{
return x_15;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_15, 0);
x_116 = lean_ctor_get(x_15, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_15);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
block_14:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_5 = x_12;
x_7 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_shutdown___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("shutdown", 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_4 = l_Lean_Lsp_Ipc_stdout(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
x_7 = l_Lean_Lsp_Ipc_stdin(x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_1);
x_10 = l_Lean_JsonNumber_fromNat(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Lsp_Ipc_shutdown___closed__1;
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_inc(x_8);
x_15 = l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_shutdown___spec__1(x_8, x_14, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5(x_1, x_5, x_8, x_11, x_17, x_2, x_16);
lean_dec(x_11);
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
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
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
lean_dec(x_3);
x_6 = l_IO_FS_Stream_readLspMessage(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Lsp_Ipc_stdout(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_FS_Stream_readLspRequestAs(x_7, x_1, lean_box(0), x_3, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("2.0", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("jsonrpc", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__3;
x_2 = l_Lean_Lsp_Ipc_readResponseAs___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("method", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("params", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC response, got: '", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected result '", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'\n", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("message", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("data", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__16;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__17;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__20;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__21;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__24;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__28;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__30;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__32;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__33;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__34;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__36;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__38;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__40;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__41;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__42;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__44;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__45;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__46;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__48;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__49;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__50;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__52;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__53;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__54;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__56;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__57;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__58;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__60;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__61;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__62;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_4);
x_6 = l_Lean_Lsp_Ipc_stdout(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_IO_FS_Stream_readLspMessage(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_12; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = l_Lean_Lsp_Ipc_readResponseAs___closed__5;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Lsp_Ipc_readResponseAs___closed__6;
x_23 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_22, x_16);
lean_dec(x_16);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
x_29 = l_List_appendTR___rarg(x_28, x_23);
x_30 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Json_mkObj(x_31);
x_33 = l_Lean_Json_compress(x_32);
x_34 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_38);
return x_10;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_21);
x_44 = l_List_appendTR___rarg(x_43, x_23);
x_45 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Json_mkObj(x_46);
x_48 = l_Lean_Json_compress(x_47);
x_49 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_53);
return x_10;
}
default: 
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = l_Lean_Lsp_Ipc_readResponseAs___closed__9;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_21);
x_56 = l_List_appendTR___rarg(x_55, x_23);
x_57 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Json_mkObj(x_58);
x_60 = l_Lean_Json_compress(x_59);
x_61 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_62 = lean_string_append(x_61, x_60);
lean_dec(x_60);
x_63 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_65);
return x_10;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_dec(x_10);
x_67 = lean_ctor_get(x_11, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_11, 2);
lean_inc(x_69);
lean_dec(x_11);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_68);
x_71 = l_Lean_Lsp_Ipc_readResponseAs___closed__5;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Lsp_Ipc_readResponseAs___closed__6;
x_76 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_75, x_69);
lean_dec(x_69);
switch (lean_obj_tag(x_67)) {
case 0:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_77 = lean_ctor_get(x_67, 0);
lean_inc(x_77);
lean_dec(x_67);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
x_82 = l_List_appendTR___rarg(x_81, x_76);
x_83 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Json_mkObj(x_84);
x_86 = l_Lean_Json_compress(x_85);
x_87 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_66);
return x_92;
}
case 1:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_93 = lean_ctor_get(x_67, 0);
lean_inc(x_93);
lean_dec(x_67);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_74);
x_98 = l_List_appendTR___rarg(x_97, x_76);
x_99 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_Json_mkObj(x_100);
x_102 = l_Lean_Json_compress(x_101);
x_103 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_104 = lean_string_append(x_103, x_102);
lean_dec(x_102);
x_105 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_106 = lean_string_append(x_104, x_105);
x_107 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_66);
return x_108;
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_109 = l_Lean_Lsp_Ipc_readResponseAs___closed__9;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_74);
x_111 = l_List_appendTR___rarg(x_110, x_76);
x_112 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Json_mkObj(x_113);
x_115 = l_Lean_Json_compress(x_114);
x_116 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_117 = lean_string_append(x_116, x_115);
lean_dec(x_115);
x_118 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_119 = lean_string_append(x_117, x_118);
x_120 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_66);
return x_121;
}
}
}
}
case 1:
{
lean_object* x_122; 
lean_dec(x_11);
lean_free_object(x_6);
x_122 = lean_ctor_get(x_10, 1);
lean_inc(x_122);
lean_dec(x_10);
x_2 = lean_box(0);
x_5 = x_122;
goto _start;
}
case 2:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_156; 
lean_dec(x_4);
x_124 = lean_ctor_get(x_10, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_125 = x_10;
} else {
 lean_dec_ref(x_10);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_11, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_11, 1);
lean_inc(x_127);
lean_dec(x_11);
x_156 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_126, x_1);
if (x_156 == 0)
{
lean_dec(x_127);
lean_free_object(x_6);
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
lean_dec(x_1);
x_158 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_159 = lean_string_append(x_158, x_157);
lean_dec(x_157);
x_160 = lean_string_append(x_159, x_158);
x_128 = x_160;
goto block_155;
}
case 1:
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
lean_dec(x_1);
x_162 = l_Lean_JsonNumber_toString(x_161);
x_128 = x_162;
goto block_155;
}
default: 
{
lean_object* x_163; 
x_163 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_128 = x_163;
goto block_155;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_126);
lean_dec(x_125);
lean_inc(x_127);
x_164 = lean_apply_1(x_3, x_127);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_1);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l_Lean_Json_compress(x_127);
x_167 = l_Lean_Lsp_Ipc_readResponseAs___closed__10;
x_168 = lean_string_append(x_167, x_166);
lean_dec(x_166);
x_169 = l_Lean_Lsp_Ipc_readResponseAs___closed__11;
x_170 = lean_string_append(x_168, x_169);
x_171 = lean_string_append(x_170, x_165);
lean_dec(x_165);
x_172 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_173 = lean_string_append(x_171, x_172);
x_174 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_124);
lean_ctor_set(x_6, 0, x_174);
return x_6;
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_127);
x_175 = lean_ctor_get(x_164, 0);
lean_inc(x_175);
lean_dec(x_164);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_6, 1, x_124);
lean_ctor_set(x_6, 0, x_176);
return x_6;
}
}
block_155:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
x_130 = lean_string_append(x_129, x_128);
lean_dec(x_128);
x_131 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
x_132 = lean_string_append(x_130, x_131);
switch (lean_obj_tag(x_126)) {
case 0:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_126, 0);
lean_inc(x_133);
lean_dec(x_126);
x_134 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_135 = lean_string_append(x_134, x_133);
lean_dec(x_133);
x_136 = lean_string_append(x_135, x_134);
x_137 = lean_string_append(x_132, x_136);
lean_dec(x_136);
x_138 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_139 = lean_string_append(x_137, x_138);
x_140 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_140, 0, x_139);
if (lean_is_scalar(x_125)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_125;
 lean_ctor_set_tag(x_141, 1);
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_124);
return x_141;
}
case 1:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_126, 0);
lean_inc(x_142);
lean_dec(x_126);
x_143 = l_Lean_JsonNumber_toString(x_142);
x_144 = lean_string_append(x_132, x_143);
lean_dec(x_143);
x_145 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_146 = lean_string_append(x_144, x_145);
x_147 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_147, 0, x_146);
if (lean_is_scalar(x_125)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_125;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_124);
return x_148;
}
default: 
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_150 = lean_string_append(x_132, x_149);
x_151 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_153, 0, x_152);
if (lean_is_scalar(x_125)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_125;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_124);
return x_154;
}
}
}
}
default: 
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_177 = lean_ctor_get(x_10, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_178 = x_10;
} else {
 lean_dec_ref(x_10);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_11, 0);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_181 = lean_ctor_get(x_11, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_11, 2);
lean_inc(x_182);
lean_dec(x_11);
x_183 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_183, 0, x_181);
x_184 = l_Lean_Lsp_Ipc_readResponseAs___closed__12;
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_Lsp_Ipc_readResponseAs___closed__13;
x_189 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_188, x_182);
lean_dec(x_182);
switch (lean_obj_tag(x_179)) {
case 0:
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_179, 0);
lean_inc(x_227);
lean_dec(x_179);
x_228 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_190 = x_228;
goto block_226;
}
case 1:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_179, 0);
lean_inc(x_229);
lean_dec(x_179);
x_230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_190 = x_230;
goto block_226;
}
default: 
{
lean_object* x_231; 
x_231 = lean_box(0);
x_190 = x_231;
goto block_226;
}
}
block_226:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
switch (x_180) {
case 0:
{
lean_object* x_214; 
x_214 = l_Lean_Lsp_Ipc_readResponseAs___closed__19;
x_193 = x_214;
goto block_213;
}
case 1:
{
lean_object* x_215; 
x_215 = l_Lean_Lsp_Ipc_readResponseAs___closed__23;
x_193 = x_215;
goto block_213;
}
case 2:
{
lean_object* x_216; 
x_216 = l_Lean_Lsp_Ipc_readResponseAs___closed__27;
x_193 = x_216;
goto block_213;
}
case 3:
{
lean_object* x_217; 
x_217 = l_Lean_Lsp_Ipc_readResponseAs___closed__31;
x_193 = x_217;
goto block_213;
}
case 4:
{
lean_object* x_218; 
x_218 = l_Lean_Lsp_Ipc_readResponseAs___closed__35;
x_193 = x_218;
goto block_213;
}
case 5:
{
lean_object* x_219; 
x_219 = l_Lean_Lsp_Ipc_readResponseAs___closed__39;
x_193 = x_219;
goto block_213;
}
case 6:
{
lean_object* x_220; 
x_220 = l_Lean_Lsp_Ipc_readResponseAs___closed__43;
x_193 = x_220;
goto block_213;
}
case 7:
{
lean_object* x_221; 
x_221 = l_Lean_Lsp_Ipc_readResponseAs___closed__47;
x_193 = x_221;
goto block_213;
}
case 8:
{
lean_object* x_222; 
x_222 = l_Lean_Lsp_Ipc_readResponseAs___closed__51;
x_193 = x_222;
goto block_213;
}
case 9:
{
lean_object* x_223; 
x_223 = l_Lean_Lsp_Ipc_readResponseAs___closed__55;
x_193 = x_223;
goto block_213;
}
case 10:
{
lean_object* x_224; 
x_224 = l_Lean_Lsp_Ipc_readResponseAs___closed__59;
x_193 = x_224;
goto block_213;
}
default: 
{
lean_object* x_225; 
x_225 = l_Lean_Lsp_Ipc_readResponseAs___closed__63;
x_193 = x_225;
goto block_213;
}
}
block_213:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_194 = l_Lean_Lsp_Ipc_readResponseAs___closed__14;
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_187);
x_197 = l_List_appendTR___rarg(x_196, x_189);
x_198 = l_Lean_Json_mkObj(x_197);
x_199 = l_Lean_Lsp_Ipc_readResponseAs___closed__15;
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_186);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = l_Lean_Json_mkObj(x_204);
x_206 = l_Lean_Json_compress(x_205);
x_207 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_208 = lean_string_append(x_207, x_206);
lean_dec(x_206);
x_209 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_210 = lean_string_append(x_208, x_209);
x_211 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_211, 0, x_210);
if (lean_is_scalar(x_178)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_178;
 lean_ctor_set_tag(x_212, 1);
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_177);
return x_212;
}
}
}
}
}
else
{
uint8_t x_232; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_10);
if (x_232 == 0)
{
return x_10;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_10, 0);
x_234 = lean_ctor_get(x_10, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_10);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_6, 0);
x_237 = lean_ctor_get(x_6, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_6);
x_238 = l_IO_FS_Stream_readLspMessage(x_236, x_237);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
switch (lean_obj_tag(x_239)) {
case 0:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_241 = x_238;
} else {
 lean_dec_ref(x_238);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 2);
lean_inc(x_244);
lean_dec(x_239);
x_245 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_245, 0, x_243);
x_246 = l_Lean_Lsp_Ipc_readResponseAs___closed__5;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = lean_box(0);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Lean_Lsp_Ipc_readResponseAs___closed__6;
x_251 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_250, x_244);
lean_dec(x_244);
switch (lean_obj_tag(x_242)) {
case 0:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_252 = lean_ctor_get(x_242, 0);
lean_inc(x_252);
lean_dec(x_242);
x_253 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_253, 0, x_252);
x_254 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_249);
x_257 = l_List_appendTR___rarg(x_256, x_251);
x_258 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = l_Lean_Json_mkObj(x_259);
x_261 = l_Lean_Json_compress(x_260);
x_262 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_263 = lean_string_append(x_262, x_261);
lean_dec(x_261);
x_264 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_265 = lean_string_append(x_263, x_264);
x_266 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_266, 0, x_265);
if (lean_is_scalar(x_241)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_241;
 lean_ctor_set_tag(x_267, 1);
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_240);
return x_267;
}
case 1:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_268 = lean_ctor_get(x_242, 0);
lean_inc(x_268);
lean_dec(x_242);
x_269 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_249);
x_273 = l_List_appendTR___rarg(x_272, x_251);
x_274 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l_Lean_Json_mkObj(x_275);
x_277 = l_Lean_Json_compress(x_276);
x_278 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_279 = lean_string_append(x_278, x_277);
lean_dec(x_277);
x_280 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_281 = lean_string_append(x_279, x_280);
x_282 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_282, 0, x_281);
if (lean_is_scalar(x_241)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_241;
 lean_ctor_set_tag(x_283, 1);
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_240);
return x_283;
}
default: 
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_284 = l_Lean_Lsp_Ipc_readResponseAs___closed__9;
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_249);
x_286 = l_List_appendTR___rarg(x_285, x_251);
x_287 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = l_Lean_Json_mkObj(x_288);
x_290 = l_Lean_Json_compress(x_289);
x_291 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_292 = lean_string_append(x_291, x_290);
lean_dec(x_290);
x_293 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_294 = lean_string_append(x_292, x_293);
x_295 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_295, 0, x_294);
if (lean_is_scalar(x_241)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_241;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_240);
return x_296;
}
}
}
case 1:
{
lean_object* x_297; 
lean_dec(x_239);
x_297 = lean_ctor_get(x_238, 1);
lean_inc(x_297);
lean_dec(x_238);
x_2 = lean_box(0);
x_5 = x_297;
goto _start;
}
case 2:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_331; 
lean_dec(x_4);
x_299 = lean_ctor_get(x_238, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_300 = x_238;
} else {
 lean_dec_ref(x_238);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_239, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_239, 1);
lean_inc(x_302);
lean_dec(x_239);
x_331 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_301, x_1);
if (x_331 == 0)
{
lean_dec(x_302);
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_1, 0);
lean_inc(x_332);
lean_dec(x_1);
x_333 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_334 = lean_string_append(x_333, x_332);
lean_dec(x_332);
x_335 = lean_string_append(x_334, x_333);
x_303 = x_335;
goto block_330;
}
case 1:
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_1, 0);
lean_inc(x_336);
lean_dec(x_1);
x_337 = l_Lean_JsonNumber_toString(x_336);
x_303 = x_337;
goto block_330;
}
default: 
{
lean_object* x_338; 
x_338 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_303 = x_338;
goto block_330;
}
}
}
else
{
lean_object* x_339; 
lean_dec(x_301);
lean_dec(x_300);
lean_inc(x_302);
x_339 = lean_apply_1(x_3, x_302);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_1);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec(x_339);
x_341 = l_Lean_Json_compress(x_302);
x_342 = l_Lean_Lsp_Ipc_readResponseAs___closed__10;
x_343 = lean_string_append(x_342, x_341);
lean_dec(x_341);
x_344 = l_Lean_Lsp_Ipc_readResponseAs___closed__11;
x_345 = lean_string_append(x_343, x_344);
x_346 = lean_string_append(x_345, x_340);
lean_dec(x_340);
x_347 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_348 = lean_string_append(x_346, x_347);
x_349 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_299);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_302);
x_351 = lean_ctor_get(x_339, 0);
lean_inc(x_351);
lean_dec(x_339);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_1);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_299);
return x_353;
}
}
block_330:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
x_305 = lean_string_append(x_304, x_303);
lean_dec(x_303);
x_306 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
x_307 = lean_string_append(x_305, x_306);
switch (lean_obj_tag(x_301)) {
case 0:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_308 = lean_ctor_get(x_301, 0);
lean_inc(x_308);
lean_dec(x_301);
x_309 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_310 = lean_string_append(x_309, x_308);
lean_dec(x_308);
x_311 = lean_string_append(x_310, x_309);
x_312 = lean_string_append(x_307, x_311);
lean_dec(x_311);
x_313 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_314 = lean_string_append(x_312, x_313);
x_315 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_315, 0, x_314);
if (lean_is_scalar(x_300)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_300;
 lean_ctor_set_tag(x_316, 1);
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_299);
return x_316;
}
case 1:
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_301, 0);
lean_inc(x_317);
lean_dec(x_301);
x_318 = l_Lean_JsonNumber_toString(x_317);
x_319 = lean_string_append(x_307, x_318);
lean_dec(x_318);
x_320 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_321 = lean_string_append(x_319, x_320);
x_322 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_322, 0, x_321);
if (lean_is_scalar(x_300)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_300;
 lean_ctor_set_tag(x_323, 1);
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_299);
return x_323;
}
default: 
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_325 = lean_string_append(x_307, x_324);
x_326 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_327 = lean_string_append(x_325, x_326);
x_328 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_328, 0, x_327);
if (lean_is_scalar(x_300)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_300;
 lean_ctor_set_tag(x_329, 1);
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_299);
return x_329;
}
}
}
}
default: 
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_354 = lean_ctor_get(x_238, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_355 = x_238;
} else {
 lean_dec_ref(x_238);
 x_355 = lean_box(0);
}
x_356 = lean_ctor_get(x_239, 0);
lean_inc(x_356);
x_357 = lean_ctor_get_uint8(x_239, sizeof(void*)*3);
x_358 = lean_ctor_get(x_239, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_239, 2);
lean_inc(x_359);
lean_dec(x_239);
x_360 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_360, 0, x_358);
x_361 = l_Lean_Lsp_Ipc_readResponseAs___closed__12;
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_360);
x_363 = lean_box(0);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_365 = l_Lean_Lsp_Ipc_readResponseAs___closed__13;
x_366 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_365, x_359);
lean_dec(x_359);
switch (lean_obj_tag(x_356)) {
case 0:
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_356, 0);
lean_inc(x_404);
lean_dec(x_356);
x_405 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_367 = x_405;
goto block_403;
}
case 1:
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_356, 0);
lean_inc(x_406);
lean_dec(x_356);
x_407 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_407, 0, x_406);
x_367 = x_407;
goto block_403;
}
default: 
{
lean_object* x_408; 
x_408 = lean_box(0);
x_367 = x_408;
goto block_403;
}
}
block_403:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
switch (x_357) {
case 0:
{
lean_object* x_391; 
x_391 = l_Lean_Lsp_Ipc_readResponseAs___closed__19;
x_370 = x_391;
goto block_390;
}
case 1:
{
lean_object* x_392; 
x_392 = l_Lean_Lsp_Ipc_readResponseAs___closed__23;
x_370 = x_392;
goto block_390;
}
case 2:
{
lean_object* x_393; 
x_393 = l_Lean_Lsp_Ipc_readResponseAs___closed__27;
x_370 = x_393;
goto block_390;
}
case 3:
{
lean_object* x_394; 
x_394 = l_Lean_Lsp_Ipc_readResponseAs___closed__31;
x_370 = x_394;
goto block_390;
}
case 4:
{
lean_object* x_395; 
x_395 = l_Lean_Lsp_Ipc_readResponseAs___closed__35;
x_370 = x_395;
goto block_390;
}
case 5:
{
lean_object* x_396; 
x_396 = l_Lean_Lsp_Ipc_readResponseAs___closed__39;
x_370 = x_396;
goto block_390;
}
case 6:
{
lean_object* x_397; 
x_397 = l_Lean_Lsp_Ipc_readResponseAs___closed__43;
x_370 = x_397;
goto block_390;
}
case 7:
{
lean_object* x_398; 
x_398 = l_Lean_Lsp_Ipc_readResponseAs___closed__47;
x_370 = x_398;
goto block_390;
}
case 8:
{
lean_object* x_399; 
x_399 = l_Lean_Lsp_Ipc_readResponseAs___closed__51;
x_370 = x_399;
goto block_390;
}
case 9:
{
lean_object* x_400; 
x_400 = l_Lean_Lsp_Ipc_readResponseAs___closed__55;
x_370 = x_400;
goto block_390;
}
case 10:
{
lean_object* x_401; 
x_401 = l_Lean_Lsp_Ipc_readResponseAs___closed__59;
x_370 = x_401;
goto block_390;
}
default: 
{
lean_object* x_402; 
x_402 = l_Lean_Lsp_Ipc_readResponseAs___closed__63;
x_370 = x_402;
goto block_390;
}
}
block_390:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_371 = l_Lean_Lsp_Ipc_readResponseAs___closed__14;
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_364);
x_374 = l_List_appendTR___rarg(x_373, x_366);
x_375 = l_Lean_Json_mkObj(x_374);
x_376 = l_Lean_Lsp_Ipc_readResponseAs___closed__15;
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_363);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_369);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
x_382 = l_Lean_Json_mkObj(x_381);
x_383 = l_Lean_Json_compress(x_382);
x_384 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_385 = lean_string_append(x_384, x_383);
lean_dec(x_383);
x_386 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_387 = lean_string_append(x_385, x_386);
x_388 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_388, 0, x_387);
if (lean_is_scalar(x_355)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_355;
 lean_ctor_set_tag(x_389, 1);
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_354);
return x_389;
}
}
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_409 = lean_ctor_get(x_238, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_238, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_411 = x_238;
} else {
 lean_dec_ref(x_238);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
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
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/publishDiagnostics", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot decode publishDiagnostics parameters\n", 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Waiting for diagnostics failed: ", 32);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
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
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_3 = x_6;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_14 = lean_string_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_12);
lean_free_object(x_4);
x_3 = x_9;
goto _start;
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_free_object(x_4);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1783_(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_4);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_27);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
lean_dec(x_17);
x_43 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1783_(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_50);
return x_4;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_4);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
x_52 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_51);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_51);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_51);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_dec(x_4);
x_67 = lean_ctor_get(x_5, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
lean_dec(x_5);
x_69 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_70 = lean_string_dec_eq(x_67, x_69);
lean_dec(x_67);
if (x_70 == 0)
{
lean_dec(x_68);
x_3 = x_66;
goto _start;
}
else
{
if (lean_obj_tag(x_68) == 0)
{
x_3 = x_66;
goto _start;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1783_(x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_2);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_66);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
lean_dec(x_76);
x_85 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_66);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
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
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_69);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
if (lean_is_scalar(x_88)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_88;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_84);
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_94 = x_85;
} else {
 lean_dec_ref(x_85);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_73, 0);
lean_inc(x_96);
lean_dec(x_73);
x_97 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1783_(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_101 = lean_string_append(x_100, x_99);
lean_dec(x_99);
x_102 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_66);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
lean_dec(x_98);
x_107 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_66);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_69);
lean_ctor_set(x_111, 1, x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_106);
x_114 = lean_ctor_get(x_107, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_116 = x_107;
} else {
 lean_dec_ref(x_107);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
}
}
case 2:
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_4, 1);
x_120 = lean_ctor_get(x_4, 0);
lean_dec(x_120);
x_121 = lean_ctor_get(x_5, 0);
lean_inc(x_121);
lean_dec(x_5);
x_122 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_121, x_1);
lean_dec(x_121);
if (x_122 == 0)
{
lean_free_object(x_4);
x_3 = x_119;
goto _start;
}
else
{
lean_object* x_124; 
lean_dec(x_2);
x_124 = lean_box(0);
lean_ctor_set(x_4, 0, x_124);
return x_4;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_4, 1);
lean_inc(x_125);
lean_dec(x_4);
x_126 = lean_ctor_get(x_5, 0);
lean_inc(x_126);
lean_dec(x_5);
x_127 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_126, x_1);
lean_dec(x_126);
if (x_127 == 0)
{
x_3 = x_125;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_2);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
return x_130;
}
}
}
default: 
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_4);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_4, 1);
x_133 = lean_ctor_get(x_4, 0);
lean_dec(x_133);
x_134 = lean_ctor_get(x_5, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_5, 1);
lean_inc(x_135);
lean_dec(x_5);
x_136 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_134, x_1);
lean_dec(x_134);
if (x_136 == 0)
{
lean_dec(x_135);
lean_free_object(x_4);
x_3 = x_132;
goto _start;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_2);
x_138 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
x_139 = lean_string_append(x_138, x_135);
lean_dec(x_135);
x_140 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_142);
return x_4;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_4, 1);
lean_inc(x_143);
lean_dec(x_4);
x_144 = lean_ctor_get(x_5, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_5, 1);
lean_inc(x_145);
lean_dec(x_5);
x_146 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_144, x_1);
lean_dec(x_144);
if (x_146 == 0)
{
lean_dec(x_145);
x_3 = x_143;
goto _start;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
x_148 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
x_149 = lean_string_append(x_148, x_145);
lean_dec(x_145);
x_150 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_151 = lean_string_append(x_149, x_150);
x_152 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_143);
return x_153;
}
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_2);
x_154 = !lean_is_exclusive(x_4);
if (x_154 == 0)
{
return x_4;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_4, 0);
x_156 = lean_ctor_get(x_4, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_4);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_445_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Lsp_Ipc_stdin(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(x_5, x_1, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/waitForDiagnostics", 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
lean_inc(x_4);
x_9 = l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_4, x_10);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Lsp_Ipc_runWith___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_box(0);
x_6 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_7 = l_Lean_Lsp_Ipc_runWith___rarg___closed__1;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = lean_io_process_spawn(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_2(x_3, x_11, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_runWith___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Ipc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
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
l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1 = _init_l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1);
l_Lean_Lsp_Ipc_ipcStdioConfig = _init_l_Lean_Lsp_Ipc_ipcStdioConfig();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig);
l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1);
l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2);
l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1 = _init_l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1);
l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2 = _init_l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2();
lean_mark_persistent(l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11);
l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12 = _init_l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12);
l_Lean_Lsp_Ipc_shutdown___closed__1 = _init_l_Lean_Lsp_Ipc_shutdown___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_shutdown___closed__1);
l_Lean_Lsp_Ipc_readResponseAs___closed__1 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__1);
l_Lean_Lsp_Ipc_readResponseAs___closed__2 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__2();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__2);
l_Lean_Lsp_Ipc_readResponseAs___closed__3 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__3();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__3);
l_Lean_Lsp_Ipc_readResponseAs___closed__4 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__4();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__4);
l_Lean_Lsp_Ipc_readResponseAs___closed__5 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__5();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__5);
l_Lean_Lsp_Ipc_readResponseAs___closed__6 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__6();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__6);
l_Lean_Lsp_Ipc_readResponseAs___closed__7 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__7();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__7);
l_Lean_Lsp_Ipc_readResponseAs___closed__8 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__8();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__8);
l_Lean_Lsp_Ipc_readResponseAs___closed__9 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__9();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__9);
l_Lean_Lsp_Ipc_readResponseAs___closed__10 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__10();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__10);
l_Lean_Lsp_Ipc_readResponseAs___closed__11 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__11();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__11);
l_Lean_Lsp_Ipc_readResponseAs___closed__12 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__12();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__12);
l_Lean_Lsp_Ipc_readResponseAs___closed__13 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__13();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__13);
l_Lean_Lsp_Ipc_readResponseAs___closed__14 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__14();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__14);
l_Lean_Lsp_Ipc_readResponseAs___closed__15 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__15();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__15);
l_Lean_Lsp_Ipc_readResponseAs___closed__16 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__16();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__16);
l_Lean_Lsp_Ipc_readResponseAs___closed__17 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__17();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__17);
l_Lean_Lsp_Ipc_readResponseAs___closed__18 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__18();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__18);
l_Lean_Lsp_Ipc_readResponseAs___closed__19 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__19();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__19);
l_Lean_Lsp_Ipc_readResponseAs___closed__20 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__20();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__20);
l_Lean_Lsp_Ipc_readResponseAs___closed__21 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__21();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__21);
l_Lean_Lsp_Ipc_readResponseAs___closed__22 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__22();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__22);
l_Lean_Lsp_Ipc_readResponseAs___closed__23 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__23();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__23);
l_Lean_Lsp_Ipc_readResponseAs___closed__24 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__24();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__24);
l_Lean_Lsp_Ipc_readResponseAs___closed__25 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__25();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__25);
l_Lean_Lsp_Ipc_readResponseAs___closed__26 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__26();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__26);
l_Lean_Lsp_Ipc_readResponseAs___closed__27 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__27();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__27);
l_Lean_Lsp_Ipc_readResponseAs___closed__28 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__28();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__28);
l_Lean_Lsp_Ipc_readResponseAs___closed__29 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__29();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__29);
l_Lean_Lsp_Ipc_readResponseAs___closed__30 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__30();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__30);
l_Lean_Lsp_Ipc_readResponseAs___closed__31 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__31();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__31);
l_Lean_Lsp_Ipc_readResponseAs___closed__32 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__32();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__32);
l_Lean_Lsp_Ipc_readResponseAs___closed__33 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__33();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__33);
l_Lean_Lsp_Ipc_readResponseAs___closed__34 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__34();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__34);
l_Lean_Lsp_Ipc_readResponseAs___closed__35 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__35();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__35);
l_Lean_Lsp_Ipc_readResponseAs___closed__36 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__36();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__36);
l_Lean_Lsp_Ipc_readResponseAs___closed__37 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__37();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__37);
l_Lean_Lsp_Ipc_readResponseAs___closed__38 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__38();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__38);
l_Lean_Lsp_Ipc_readResponseAs___closed__39 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__39();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__39);
l_Lean_Lsp_Ipc_readResponseAs___closed__40 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__40();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__40);
l_Lean_Lsp_Ipc_readResponseAs___closed__41 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__41();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__41);
l_Lean_Lsp_Ipc_readResponseAs___closed__42 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__42();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__42);
l_Lean_Lsp_Ipc_readResponseAs___closed__43 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__43();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__43);
l_Lean_Lsp_Ipc_readResponseAs___closed__44 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__44();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__44);
l_Lean_Lsp_Ipc_readResponseAs___closed__45 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__45();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__45);
l_Lean_Lsp_Ipc_readResponseAs___closed__46 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__46();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__46);
l_Lean_Lsp_Ipc_readResponseAs___closed__47 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__47();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__47);
l_Lean_Lsp_Ipc_readResponseAs___closed__48 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__48();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__48);
l_Lean_Lsp_Ipc_readResponseAs___closed__49 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__49();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__49);
l_Lean_Lsp_Ipc_readResponseAs___closed__50 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__50();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__50);
l_Lean_Lsp_Ipc_readResponseAs___closed__51 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__51();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__51);
l_Lean_Lsp_Ipc_readResponseAs___closed__52 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__52();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__52);
l_Lean_Lsp_Ipc_readResponseAs___closed__53 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__53();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__53);
l_Lean_Lsp_Ipc_readResponseAs___closed__54 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__54();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__54);
l_Lean_Lsp_Ipc_readResponseAs___closed__55 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__55();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__55);
l_Lean_Lsp_Ipc_readResponseAs___closed__56 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__56();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__56);
l_Lean_Lsp_Ipc_readResponseAs___closed__57 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__57();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__57);
l_Lean_Lsp_Ipc_readResponseAs___closed__58 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__58();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__58);
l_Lean_Lsp_Ipc_readResponseAs___closed__59 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__59();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__59);
l_Lean_Lsp_Ipc_readResponseAs___closed__60 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__60();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__60);
l_Lean_Lsp_Ipc_readResponseAs___closed__61 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__61();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__61);
l_Lean_Lsp_Ipc_readResponseAs___closed__62 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__62();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__62);
l_Lean_Lsp_Ipc_readResponseAs___closed__63 = _init_l_Lean_Lsp_Ipc_readResponseAs___closed__63();
lean_mark_persistent(l_Lean_Lsp_Ipc_readResponseAs___closed__63);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3);
l_Lean_Lsp_Ipc_collectDiagnostics___closed__1 = _init_l_Lean_Lsp_Ipc_collectDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics___closed__1);
l_Lean_Lsp_Ipc_runWith___rarg___closed__1 = _init_l_Lean_Lsp_Ipc_runWith___rarg___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_runWith___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

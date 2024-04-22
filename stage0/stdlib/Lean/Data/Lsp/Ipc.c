// Lean compiler output
// Module: Lean.Data.Lsp.Ipc
// Imports: Init.System.IO Lean.Data.Json Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra
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
lean_object* l_EStateM_instInhabited___rarg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__31;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__34;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__32;
static lean_object* l_Lean_Lsp_Ipc_readResponseAs___closed__30;
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
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(lean_object*);
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
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
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
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabited___rarg), 2, 1);
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
x_3 = lean_unsigned_to_nat(51u);
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
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
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
x_77 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
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
x_1 = lean_mk_string_from_bytes("Unexpected result '", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'\n", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("2.0", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("jsonrpc", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__5;
x_2 = l_Lean_Lsp_Ipc_readResponseAs___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("message", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("data", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC response, got: '", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__13;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__17;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__18;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__21;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__22;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__25;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__29;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__30;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__33;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__34;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__35;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__37;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__38;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__39;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__41;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__42;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__43;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__45;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__46;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__47;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__49;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__50;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__51;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__53;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__54;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__55;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__57;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__58;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_readResponseAs___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_readResponseAs___closed__59;
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
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_44; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_44 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_14, x_1);
if (x_44 == 0)
{
lean_dec(x_15);
lean_free_object(x_6);
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = lean_string_append(x_47, x_46);
x_16 = x_48;
goto block_43;
}
case 1:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = l_Lean_JsonNumber_toString(x_49);
x_16 = x_50;
goto block_43;
}
default: 
{
lean_object* x_51; 
x_51 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_16 = x_51;
goto block_43;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_15);
x_52 = lean_apply_1(x_3, x_15);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Json_compress(x_15);
x_55 = l_Lean_Lsp_Ipc_readResponseAs___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lean_Lsp_Ipc_readResponseAs___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_53);
lean_dec(x_53);
x_60 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_62);
return x_6;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_15);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_6, 1, x_12);
lean_ctor_set(x_6, 0, x_64);
return x_6;
}
}
block_43:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
x_20 = lean_string_append(x_18, x_19);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_string_append(x_23, x_22);
x_25 = lean_string_append(x_20, x_24);
lean_dec(x_24);
x_26 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_13)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_13;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = l_Lean_JsonNumber_toString(x_30);
x_32 = lean_string_append(x_20, x_31);
lean_dec(x_31);
x_33 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
if (lean_is_scalar(x_13)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_13;
 lean_ctor_set_tag(x_36, 1);
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_38 = lean_string_append(x_20, x_37);
x_39 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_13)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_13;
 lean_ctor_set_tag(x_42, 1);
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
}
}
}
case 3:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_66 = x_10;
} else {
 lean_dec_ref(x_10);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_11, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_69 = lean_ctor_get(x_11, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_11, 2);
lean_inc(x_70);
lean_dec(x_11);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_69);
x_72 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_77 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_76, x_70);
lean_dec(x_70);
switch (lean_obj_tag(x_67)) {
case 0:
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_67, 0);
lean_inc(x_115);
lean_dec(x_67);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_78 = x_116;
goto block_114;
}
case 1:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_67, 0);
lean_inc(x_117);
lean_dec(x_67);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_78 = x_118;
goto block_114;
}
default: 
{
lean_object* x_119; 
x_119 = lean_box(0);
x_78 = x_119;
goto block_114;
}
}
block_114:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = l_Lean_Lsp_Ipc_readResponseAs___closed__9;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
switch (x_68) {
case 0:
{
lean_object* x_102; 
x_102 = l_Lean_Lsp_Ipc_readResponseAs___closed__16;
x_81 = x_102;
goto block_101;
}
case 1:
{
lean_object* x_103; 
x_103 = l_Lean_Lsp_Ipc_readResponseAs___closed__20;
x_81 = x_103;
goto block_101;
}
case 2:
{
lean_object* x_104; 
x_104 = l_Lean_Lsp_Ipc_readResponseAs___closed__24;
x_81 = x_104;
goto block_101;
}
case 3:
{
lean_object* x_105; 
x_105 = l_Lean_Lsp_Ipc_readResponseAs___closed__28;
x_81 = x_105;
goto block_101;
}
case 4:
{
lean_object* x_106; 
x_106 = l_Lean_Lsp_Ipc_readResponseAs___closed__32;
x_81 = x_106;
goto block_101;
}
case 5:
{
lean_object* x_107; 
x_107 = l_Lean_Lsp_Ipc_readResponseAs___closed__36;
x_81 = x_107;
goto block_101;
}
case 6:
{
lean_object* x_108; 
x_108 = l_Lean_Lsp_Ipc_readResponseAs___closed__40;
x_81 = x_108;
goto block_101;
}
case 7:
{
lean_object* x_109; 
x_109 = l_Lean_Lsp_Ipc_readResponseAs___closed__44;
x_81 = x_109;
goto block_101;
}
case 8:
{
lean_object* x_110; 
x_110 = l_Lean_Lsp_Ipc_readResponseAs___closed__48;
x_81 = x_110;
goto block_101;
}
case 9:
{
lean_object* x_111; 
x_111 = l_Lean_Lsp_Ipc_readResponseAs___closed__52;
x_81 = x_111;
goto block_101;
}
case 10:
{
lean_object* x_112; 
x_112 = l_Lean_Lsp_Ipc_readResponseAs___closed__56;
x_81 = x_112;
goto block_101;
}
default: 
{
lean_object* x_113; 
x_113 = l_Lean_Lsp_Ipc_readResponseAs___closed__60;
x_81 = x_113;
goto block_101;
}
}
block_101:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_82 = l_Lean_Lsp_Ipc_readResponseAs___closed__10;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_75);
x_85 = l_List_appendTR___rarg(x_84, x_77);
x_86 = l_Lean_Json_mkObj(x_85);
x_87 = l_Lean_Lsp_Ipc_readResponseAs___closed__11;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_74);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Lsp_Ipc_readResponseAs___closed__6;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Json_mkObj(x_92);
x_94 = l_Lean_Json_compress(x_93);
x_95 = l_Lean_Lsp_Ipc_readResponseAs___closed__12;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_98 = lean_string_append(x_96, x_97);
x_99 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_66)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_66;
 lean_ctor_set_tag(x_100, 1);
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_65);
return x_100;
}
}
}
default: 
{
lean_object* x_120; 
lean_dec(x_11);
lean_free_object(x_6);
x_120 = lean_ctor_get(x_10, 1);
lean_inc(x_120);
lean_dec(x_10);
x_2 = lean_box(0);
x_5 = x_120;
goto _start;
}
}
}
else
{
uint8_t x_122; 
lean_free_object(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_10);
if (x_122 == 0)
{
return x_10;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_10, 0);
x_124 = lean_ctor_get(x_10, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_10);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_6, 0);
x_127 = lean_ctor_get(x_6, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_6);
x_128 = l_IO_FS_Stream_readLspMessage(x_126, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
switch (lean_obj_tag(x_129)) {
case 2:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_162; 
lean_dec(x_4);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_162 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_132, x_1);
if (x_162 == 0)
{
lean_dec(x_133);
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
lean_dec(x_1);
x_164 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_165 = lean_string_append(x_164, x_163);
lean_dec(x_163);
x_166 = lean_string_append(x_165, x_164);
x_134 = x_166;
goto block_161;
}
case 1:
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_1, 0);
lean_inc(x_167);
lean_dec(x_1);
x_168 = l_Lean_JsonNumber_toString(x_167);
x_134 = x_168;
goto block_161;
}
default: 
{
lean_object* x_169; 
x_169 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_134 = x_169;
goto block_161;
}
}
}
else
{
lean_object* x_170; 
lean_dec(x_132);
lean_dec(x_131);
lean_inc(x_133);
x_170 = lean_apply_1(x_3, x_133);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_1);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Lean_Json_compress(x_133);
x_173 = l_Lean_Lsp_Ipc_readResponseAs___closed__1;
x_174 = lean_string_append(x_173, x_172);
lean_dec(x_172);
x_175 = l_Lean_Lsp_Ipc_readResponseAs___closed__2;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_string_append(x_176, x_171);
lean_dec(x_171);
x_178 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_179 = lean_string_append(x_177, x_178);
x_180 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_130);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_133);
x_182 = lean_ctor_get(x_170, 0);
lean_inc(x_182);
lean_dec(x_170);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_130);
return x_184;
}
}
block_161:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
x_138 = lean_string_append(x_136, x_137);
switch (lean_obj_tag(x_132)) {
case 0:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_132, 0);
lean_inc(x_139);
lean_dec(x_132);
x_140 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = lean_string_append(x_141, x_140);
x_143 = lean_string_append(x_138, x_142);
lean_dec(x_142);
x_144 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_145 = lean_string_append(x_143, x_144);
x_146 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_131)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_131;
 lean_ctor_set_tag(x_147, 1);
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_130);
return x_147;
}
case 1:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_132, 0);
lean_inc(x_148);
lean_dec(x_132);
x_149 = l_Lean_JsonNumber_toString(x_148);
x_150 = lean_string_append(x_138, x_149);
lean_dec(x_149);
x_151 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_153, 0, x_152);
if (lean_is_scalar(x_131)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_131;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_130);
return x_154;
}
default: 
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
x_156 = lean_string_append(x_138, x_155);
x_157 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_159, 0, x_158);
if (lean_is_scalar(x_131)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_131;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_130);
return x_160;
}
}
}
}
case 3:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_185 = lean_ctor_get(x_128, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_186 = x_128;
} else {
 lean_dec_ref(x_128);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_129, 0);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_129, sizeof(void*)*3);
x_189 = lean_ctor_get(x_129, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_129, 2);
lean_inc(x_190);
lean_dec(x_129);
x_191 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_191, 0, x_189);
x_192 = l_Lean_Lsp_Ipc_readResponseAs___closed__7;
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Lsp_Ipc_readResponseAs___closed__8;
x_197 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_196, x_190);
lean_dec(x_190);
switch (lean_obj_tag(x_187)) {
case 0:
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_187, 0);
lean_inc(x_235);
lean_dec(x_187);
x_236 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_198 = x_236;
goto block_234;
}
case 1:
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_187, 0);
lean_inc(x_237);
lean_dec(x_187);
x_238 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_238, 0, x_237);
x_198 = x_238;
goto block_234;
}
default: 
{
lean_object* x_239; 
x_239 = lean_box(0);
x_198 = x_239;
goto block_234;
}
}
block_234:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = l_Lean_Lsp_Ipc_readResponseAs___closed__9;
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
switch (x_188) {
case 0:
{
lean_object* x_222; 
x_222 = l_Lean_Lsp_Ipc_readResponseAs___closed__16;
x_201 = x_222;
goto block_221;
}
case 1:
{
lean_object* x_223; 
x_223 = l_Lean_Lsp_Ipc_readResponseAs___closed__20;
x_201 = x_223;
goto block_221;
}
case 2:
{
lean_object* x_224; 
x_224 = l_Lean_Lsp_Ipc_readResponseAs___closed__24;
x_201 = x_224;
goto block_221;
}
case 3:
{
lean_object* x_225; 
x_225 = l_Lean_Lsp_Ipc_readResponseAs___closed__28;
x_201 = x_225;
goto block_221;
}
case 4:
{
lean_object* x_226; 
x_226 = l_Lean_Lsp_Ipc_readResponseAs___closed__32;
x_201 = x_226;
goto block_221;
}
case 5:
{
lean_object* x_227; 
x_227 = l_Lean_Lsp_Ipc_readResponseAs___closed__36;
x_201 = x_227;
goto block_221;
}
case 6:
{
lean_object* x_228; 
x_228 = l_Lean_Lsp_Ipc_readResponseAs___closed__40;
x_201 = x_228;
goto block_221;
}
case 7:
{
lean_object* x_229; 
x_229 = l_Lean_Lsp_Ipc_readResponseAs___closed__44;
x_201 = x_229;
goto block_221;
}
case 8:
{
lean_object* x_230; 
x_230 = l_Lean_Lsp_Ipc_readResponseAs___closed__48;
x_201 = x_230;
goto block_221;
}
case 9:
{
lean_object* x_231; 
x_231 = l_Lean_Lsp_Ipc_readResponseAs___closed__52;
x_201 = x_231;
goto block_221;
}
case 10:
{
lean_object* x_232; 
x_232 = l_Lean_Lsp_Ipc_readResponseAs___closed__56;
x_201 = x_232;
goto block_221;
}
default: 
{
lean_object* x_233; 
x_233 = l_Lean_Lsp_Ipc_readResponseAs___closed__60;
x_201 = x_233;
goto block_221;
}
}
block_221:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_202 = l_Lean_Lsp_Ipc_readResponseAs___closed__10;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_195);
x_205 = l_List_appendTR___rarg(x_204, x_197);
x_206 = l_Lean_Json_mkObj(x_205);
x_207 = l_Lean_Lsp_Ipc_readResponseAs___closed__11;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_194);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_Lsp_Ipc_readResponseAs___closed__6;
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_Lean_Json_mkObj(x_212);
x_214 = l_Lean_Json_compress(x_213);
x_215 = l_Lean_Lsp_Ipc_readResponseAs___closed__12;
x_216 = lean_string_append(x_215, x_214);
lean_dec(x_214);
x_217 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
x_218 = lean_string_append(x_216, x_217);
x_219 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_219, 0, x_218);
if (lean_is_scalar(x_186)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_186;
 lean_ctor_set_tag(x_220, 1);
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_185);
return x_220;
}
}
}
default: 
{
lean_object* x_240; 
lean_dec(x_129);
x_240 = lean_ctor_get(x_128, 1);
lean_inc(x_240);
lean_dec(x_128);
x_2 = lean_box(0);
x_5 = x_240;
goto _start;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_242 = lean_ctor_get(x_128, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_128, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_244 = x_128;
} else {
 lean_dec_ref(x_128);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
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
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_12);
lean_dec(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_4);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_12, 0, x_33);
lean_ctor_set(x_29, 0, x_12);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_12, 0, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_28);
lean_free_object(x_12);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_29, 0, x_41);
return x_29;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_44 = x_30;
} else {
 lean_dec_ref(x_30);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_28);
lean_free_object(x_12);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
lean_dec(x_18);
x_52 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_12);
lean_dec(x_2);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_59);
return x_4;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_4);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec(x_53);
x_61 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_13);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_12, 0, x_65);
lean_ctor_set(x_61, 0, x_12);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_13);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_12, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_60);
lean_free_object(x_12);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_61, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_62);
if (x_71 == 0)
{
return x_61;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_61, 0, x_73);
return x_61;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
lean_dec(x_61);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_76 = x_62;
} else {
 lean_dec_ref(x_62);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_60);
lean_free_object(x_12);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_12, 0);
lean_inc(x_83);
lean_dec(x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_92);
return x_4;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_free_object(x_4);
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
x_94 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_93);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_93);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_95, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_104 = x_95;
} else {
 lean_dec_ref(x_95);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_102;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_93);
x_107 = lean_ctor_get(x_94, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_94, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_109 = x_94;
} else {
 lean_dec_ref(x_94);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_83, 0);
lean_inc(x_111);
lean_dec(x_83);
x_112 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_116 = lean_string_append(x_115, x_114);
lean_dec(x_114);
x_117 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_119);
return x_4;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_free_object(x_4);
x_120 = lean_ctor_get(x_113, 0);
lean_inc(x_120);
lean_dec(x_113);
x_121 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_13);
lean_ctor_set(x_125, 1, x_120);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
if (lean_is_scalar(x_124)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_124;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_123);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_120);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_122, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_131 = x_122;
} else {
 lean_dec_ref(x_122);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
if (lean_is_scalar(x_129)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_129;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_120);
x_134 = lean_ctor_get(x_121, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_121, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_136 = x_121;
} else {
 lean_dec_ref(x_121);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_4, 1);
lean_inc(x_138);
lean_dec(x_4);
x_139 = lean_ctor_get(x_5, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_5, 1);
lean_inc(x_140);
lean_dec(x_5);
x_141 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_142 = lean_string_dec_eq(x_139, x_141);
lean_dec(x_139);
if (x_142 == 0)
{
lean_dec(x_140);
x_3 = x_138;
goto _start;
}
else
{
if (lean_obj_tag(x_140) == 0)
{
x_3 = x_138;
goto _start;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_146 = x_140;
} else {
 lean_dec_ref(x_140);
 x_146 = lean_box(0);
}
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_146);
lean_dec(x_2);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_152 = lean_string_append(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_154 = lean_string_append(x_152, x_153);
x_155 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_138);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_149, 0);
lean_inc(x_157);
lean_dec(x_149);
x_158 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_138);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_141);
lean_ctor_set(x_162, 1, x_157);
if (lean_is_scalar(x_146)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_146;
}
lean_ctor_set(x_163, 0, x_162);
if (lean_is_scalar(x_161)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_161;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_157);
lean_dec(x_146);
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_166 = x_158;
} else {
 lean_dec_ref(x_158);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_159, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_168 = x_159;
} else {
 lean_dec_ref(x_159);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_167);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_165);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_146);
x_171 = lean_ctor_get(x_158, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_158, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_173 = x_158;
} else {
 lean_dec_ref(x_158);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_145, 0);
lean_inc(x_175);
lean_dec(x_145);
x_176 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2430_(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_146);
lean_dec(x_2);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_180 = lean_string_append(x_179, x_178);
lean_dec(x_178);
x_181 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_138);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_177, 0);
lean_inc(x_185);
lean_dec(x_177);
x_186 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_138);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_141);
lean_ctor_set(x_190, 1, x_185);
if (lean_is_scalar(x_146)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_146;
}
lean_ctor_set(x_191, 0, x_190);
if (lean_is_scalar(x_189)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_189;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_188);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_185);
lean_dec(x_146);
x_193 = lean_ctor_get(x_186, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_187, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
if (lean_is_scalar(x_194)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_194;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_193);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_185);
lean_dec(x_146);
x_199 = lean_ctor_get(x_186, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_186, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_201 = x_186;
} else {
 lean_dec_ref(x_186);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
}
}
}
}
case 2:
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_4);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_4, 1);
x_205 = lean_ctor_get(x_4, 0);
lean_dec(x_205);
x_206 = lean_ctor_get(x_5, 0);
lean_inc(x_206);
lean_dec(x_5);
x_207 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_206, x_1);
lean_dec(x_206);
if (x_207 == 0)
{
lean_free_object(x_4);
x_3 = x_204;
goto _start;
}
else
{
lean_object* x_209; 
lean_dec(x_2);
x_209 = lean_box(0);
lean_ctor_set(x_4, 0, x_209);
return x_4;
}
}
else
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_4, 1);
lean_inc(x_210);
lean_dec(x_4);
x_211 = lean_ctor_get(x_5, 0);
lean_inc(x_211);
lean_dec(x_5);
x_212 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_211, x_1);
lean_dec(x_211);
if (x_212 == 0)
{
x_3 = x_210;
goto _start;
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_2);
x_214 = lean_box(0);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
return x_215;
}
}
}
default: 
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_4);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_4, 1);
x_218 = lean_ctor_get(x_4, 0);
lean_dec(x_218);
x_219 = lean_ctor_get(x_5, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_5, 1);
lean_inc(x_220);
lean_dec(x_5);
x_221 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_219, x_1);
lean_dec(x_219);
if (x_221 == 0)
{
lean_dec(x_220);
lean_free_object(x_4);
x_3 = x_217;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_2);
x_223 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
x_224 = lean_string_append(x_223, x_220);
lean_dec(x_220);
x_225 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_226 = lean_string_append(x_224, x_225);
x_227 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_227);
return x_4;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = lean_ctor_get(x_4, 1);
lean_inc(x_228);
lean_dec(x_4);
x_229 = lean_ctor_get(x_5, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_5, 1);
lean_inc(x_230);
lean_dec(x_5);
x_231 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_33_(x_229, x_1);
lean_dec(x_229);
if (x_231 == 0)
{
lean_dec(x_230);
x_3 = x_228;
goto _start;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_2);
x_233 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
x_234 = lean_string_append(x_233, x_230);
lean_dec(x_230);
x_235 = l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_228);
return x_238;
}
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_2);
x_239 = !lean_is_exclusive(x_4);
if (x_239 == 0)
{
return x_4;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_4, 0);
x_241 = lean_ctor_get(x_4, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_4);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
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

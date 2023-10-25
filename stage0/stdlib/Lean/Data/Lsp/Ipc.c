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
static lean_object* l_Lean_Lsp_Ipc_runWith___rarg___closed__1;
uint8_t l_Lean_Json_isNull(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__12;
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*);
static lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_shutdown(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2081_(lean_object*);
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__1;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__2;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabitedEStateM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__5;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__10;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__9;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Lsp_Ipc_shutdown___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_instInhabitedError;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__6;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_shutdown___closed__1;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_514_(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__11;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_shutdown___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___lambda__1___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__4;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__3;
static lean_object* l_panic___at_Lean_Lsp_Ipc_shutdown___spec__3___closed__2;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Lsp_Ipc_shutdown___spec__5___closed__8;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_shutdown___spec__2___closed__2;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readRequestAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_31 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_20, x_4);
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
x_76 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_65, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Lsp_Ipc_stdout(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_FS_Stream_readLspResponseAs(x_7, x_1, lean_box(0), x_3, x_8);
return x_9;
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
x_20 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2081_(x_19);
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
x_44 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2081_(x_43);
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
x_76 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2081_(x_75);
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
x_98 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_2081_(x_97);
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
x_122 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_121, x_1);
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
x_127 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_126, x_1);
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
x_136 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_134, x_1);
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
x_146 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_34_(x_144, x_1);
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
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_514_(x_1);
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

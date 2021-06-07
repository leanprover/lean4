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
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_32_(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1139_(lean_object*);
lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_runWith___rarg___closed__1;
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_23_(lean_object*);
lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4;
lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1(lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig;
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2(lean_object*);
lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*);
lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
lean_object* l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Lsp_Ipc_stdin(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Lsp_Ipc_stdout(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Lsp_Ipc_writeRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_writeRequest___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Lsp_Ipc_writeNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_writeNotification___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_4 = lean_io_process_child_wait(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Lsp_Ipc_waitForExit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Lsp_Ipc_waitForExit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/publishDiagnostics");
return x_1;
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_4);
x_11 = lean_apply_1(x_5, x_1);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_9);
x_15 = lean_apply_1(x_5, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_1);
lean_dec(x_5);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_apply_1(x_4, x_16);
return x_17;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_apply_1(x_5, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_apply_1(x_4, x_20);
return x_21;
}
}
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_2(x_2, x_22, x_23);
return x_24;
}
default: 
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_box(x_26);
x_30 = lean_apply_4(x_3, x_25, x_29, x_27, x_28);
return x_30;
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Cannot decode publishDiagnostics parameters");
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Waiting for diagnostics failed: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
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
x_20 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1139_(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_4);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_22);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1139_(x_38);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_2);
x_40 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_40);
return x_4;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_4);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_9);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_13);
lean_ctor_set(x_45, 1, x_41);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_41);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_41);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
lean_dec(x_4);
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_dec(x_5);
x_59 = l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
x_60 = lean_string_dec_eq(x_57, x_59);
lean_dec(x_57);
if (x_60 == 0)
{
lean_dec(x_58);
x_3 = x_56;
goto _start;
}
else
{
if (lean_obj_tag(x_58) == 0)
{
x_3 = x_56;
goto _start;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1139_(x_65);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_2);
x_67 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_56);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_56);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_59);
lean_ctor_set(x_74, 1, x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_79 = x_70;
} else {
 lean_dec_ref(x_70);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_63, 0);
lean_inc(x_81);
lean_dec(x_63);
x_82 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1139_(x_82);
lean_dec(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
x_84 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_56);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_56);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_59);
lean_ctor_set(x_91, 1, x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
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
}
}
}
}
}
case 2:
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_4);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_4, 1);
x_100 = lean_ctor_get(x_4, 0);
lean_dec(x_100);
x_101 = lean_ctor_get(x_5, 0);
lean_inc(x_101);
lean_dec(x_5);
x_102 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_32_(x_101, x_1);
lean_dec(x_101);
if (x_102 == 0)
{
lean_free_object(x_4);
x_3 = x_99;
goto _start;
}
else
{
lean_object* x_104; 
lean_dec(x_2);
x_104 = lean_box(0);
lean_ctor_set(x_4, 0, x_104);
return x_4;
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_4, 1);
lean_inc(x_105);
lean_dec(x_4);
x_106 = lean_ctor_get(x_5, 0);
lean_inc(x_106);
lean_dec(x_5);
x_107 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_32_(x_106, x_1);
lean_dec(x_106);
if (x_107 == 0)
{
x_3 = x_105;
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
}
}
default: 
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_4);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_4, 1);
x_113 = lean_ctor_get(x_4, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_5, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_5, 1);
lean_inc(x_115);
lean_dec(x_5);
x_116 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_32_(x_114, x_1);
lean_dec(x_114);
if (x_116 == 0)
{
lean_dec(x_115);
lean_free_object(x_4);
x_3 = x_112;
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_2);
x_118 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
x_119 = lean_string_append(x_118, x_115);
lean_dec(x_115);
x_120 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4;
x_121 = lean_string_append(x_119, x_120);
x_122 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_122);
return x_4;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_4, 1);
lean_inc(x_123);
lean_dec(x_4);
x_124 = lean_ctor_get(x_5, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_5, 1);
lean_inc(x_125);
lean_dec(x_5);
x_126 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_32_(x_124, x_1);
lean_dec(x_124);
if (x_126 == 0)
{
lean_dec(x_125);
x_3 = x_123;
goto _start;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_2);
x_128 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3;
x_129 = lean_string_append(x_128, x_125);
lean_dec(x_125);
x_130 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4;
x_131 = lean_string_append(x_129, x_130);
x_132 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_123);
return x_133;
}
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_4);
if (x_134 == 0)
{
return x_4;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_4, 0);
x_136 = lean_ctor_get(x_4, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_4);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_23_(x_1);
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
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_mk_string("textDocument/waitForDiagnostics");
return x_1;
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_7 = l_Lean_Lsp_Ipc_runWith___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_7);
x_9 = lean_io_process_spawn(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_2(x_3, x_10, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_runWith(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_runWith___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_Ipc(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1 = _init_l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1);
l_Lean_Lsp_Ipc_ipcStdioConfig = _init_l_Lean_Lsp_Ipc_ipcStdioConfig();
lean_mark_persistent(l_Lean_Lsp_Ipc_ipcStdioConfig);
l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__3);
l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4 = _init_l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__4);
l_Lean_Lsp_Ipc_collectDiagnostics___closed__1 = _init_l_Lean_Lsp_Ipc_collectDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics___closed__1);
l_Lean_Lsp_Ipc_runWith___rarg___closed__1 = _init_l_Lean_Lsp_Ipc_runWith___rarg___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_runWith___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

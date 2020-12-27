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
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_885_(lean_object*);
lean_object* l_Lean_Lsp_Ipc_readResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_stdin(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__1;
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_object* l_Lean_Lsp_Ipc_runWith(lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_stdout(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__1(lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeRequest(lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_7_(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2(lean_object*);
lean_object* l_Lean_Lsp_Ipc_readMessage(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_Ipc_writeNotification(lean_object*);
lean_object* l_Lean_Lsp_Ipc_waitForExit(lean_object*, lean_object*);
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
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
x_8 = lean_string_dec_eq(x_5, x_7);
lean_dec(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_7);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_1);
lean_dec(x_4);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_apply_1(x_3, x_14);
return x_15;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_apply_1(x_4, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_apply_1(x_3, x_18);
return x_19;
}
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_2(x_2, x_20, x_21);
return x_22;
}
default: 
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_apply_1(x_4, x_1);
return x_23;
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg), 4, 0);
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
case 1:
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
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
x_12 = lean_string_dec_eq(x_9, x_11);
lean_dec(x_9);
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
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_885_(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_4);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_7);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_20);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_20);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_885_(x_36);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_2);
x_38 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_38);
return x_4;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_4);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_7);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_11);
lean_ctor_set(x_43, 1, x_39);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_39);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_dec(x_4);
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_dec(x_5);
x_57 = l_Lean_Lsp_Ipc_collectDiagnostics_loop_match__2___rarg___closed__1;
x_58 = lean_string_dec_eq(x_55, x_57);
lean_dec(x_55);
if (x_58 == 0)
{
lean_dec(x_56);
x_3 = x_54;
goto _start;
}
else
{
if (lean_obj_tag(x_56) == 0)
{
x_3 = x_54;
goto _start;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_885_(x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
x_65 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_54);
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
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
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
lean_dec(x_67);
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
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_61, 0);
lean_inc(x_79);
lean_dec(x_61);
x_80 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_fromJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_885_(x_80);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_2);
x_82 = l_Lean_Lsp_Ipc_collectDiagnostics_loop___closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_54);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_2, x_54);
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
lean_ctor_set(x_89, 0, x_57);
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
}
}
}
}
case 2:
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_4);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_4, 1);
x_98 = lean_ctor_get(x_4, 0);
lean_dec(x_98);
x_99 = lean_ctor_get(x_5, 0);
lean_inc(x_99);
lean_dec(x_5);
x_100 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_99, x_1);
lean_dec(x_99);
if (x_100 == 0)
{
lean_free_object(x_4);
x_3 = x_97;
goto _start;
}
else
{
lean_object* x_102; 
lean_dec(x_2);
x_102 = lean_box(0);
lean_ctor_set(x_4, 0, x_102);
return x_4;
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_4, 1);
lean_inc(x_103);
lean_dec(x_4);
x_104 = lean_ctor_get(x_5, 0);
lean_inc(x_104);
lean_dec(x_5);
x_105 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_beqRequestID____x40_Lean_Data_JsonRpc___hyg_16_(x_104, x_1);
lean_dec(x_104);
if (x_105 == 0)
{
x_3 = x_103;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_2);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_103);
return x_108;
}
}
}
default: 
{
lean_object* x_109; 
lean_dec(x_5);
x_109 = lean_ctor_get(x_4, 1);
lean_inc(x_109);
lean_dec(x_4);
x_3 = x_109;
goto _start;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_4);
if (x_111 == 0)
{
return x_4;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_4, 0);
x_113 = lean_ctor_get(x_4, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_4);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
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
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_7_(x_1);
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
lean_object* l_Lean_Lsp_Ipc_collectDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
lean_inc(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_inc(x_3);
x_7 = l_Lean_Lsp_Ipc_writeRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__1(x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Lsp_Ipc_collectDiagnostics_loop(x_1, x_3, x_8);
lean_dec(x_1);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Lsp_Ipc_runWith___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = l_Lean_Lsp_Ipc_ipcStdioConfig;
x_7 = l_Array_empty___closed__1;
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
l_Lean_Lsp_Ipc_collectDiagnostics___closed__1 = _init_l_Lean_Lsp_Ipc_collectDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_Ipc_collectDiagnostics___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

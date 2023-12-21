// Lean compiler output
// Module: Lean.Server.Utils
// Imports: Init Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Lean.Data.Lsp.TextSync Lean.Server.InfoUtils
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__4(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_applyWorkspaceEdit___closed__2;
LEAN_EXPORT lean_object* l_IO_throwServerError___rarg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__1;
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonApplyWorkspaceEditParams____x40_Lean_Data_Lsp_Basic___hyg_4575_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyWorkspaceEdit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_applyWorkspaceEdit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_publishProgress___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_foldDocumentChanges___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_publishProgressAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__4(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__2;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_publishProgress(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_foldDocumentChanges___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_maybeTee___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_publishDiagnostics___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__1;
lean_object* l_Lean_FileMap_ofString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta;
static lean_object* l_Lean_Server_publishProgressAtPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_publishProgressAtPos(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_publishProgress___closed__1;
LEAN_EXPORT lean_object* l_String_Range_toLspRange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError(lean_object*);
lean_object* l_System_mkFilePath(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Range_toLspRange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_publishDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_publishProgressDone(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonLeanFileProgressParams____x40_Lean_Data_Lsp_Extra___hyg_927_(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_applyWorkspaceEdit___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_publishProgress___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_applyWorkspaceEdit___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__4;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4(lean_object*, lean_object*, uint8_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_publishDiagnostics___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_throwServerError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_throwServerError___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_5, x_6);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box_usize(x_4);
x_8 = lean_apply_2(x_6, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_inc(x_9);
x_12 = lean_apply_2(x_11, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
if (x_3 == 0)
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_1(x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_9);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_2, x_6, x_5);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_2(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
if (x_2 == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___elambda__5), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___elambda__4___boxed), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___elambda__3), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lambda__2___boxed), 4, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___elambda__2), 3, 2);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___elambda__1), 3, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_chainRight___elambda__4___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_IO_FS_Stream_chainRight___elambda__4(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_chainRight___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_IO_FS_Stream_chainRight___lambda__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_IO_FS_Stream_chainRight(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
x_8 = lean_apply_2(x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = l_IO_FS_Stream_chainLeft___elambda__1___lambda__1(x_2, x_5, x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_1(x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_chainLeft___elambda__1___lambda__1(x_2, x_5, x_14, x_15);
lean_dec(x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
x_8 = lean_apply_2(x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = l_IO_FS_Stream_chainLeft___elambda__3___lambda__1(x_2, x_5, x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_1(x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_FS_Stream_chainLeft___elambda__3___lambda__1(x_2, x_5, x_14, x_15);
lean_dec(x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box_usize(x_2);
x_6 = lean_apply_2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_2, x_6, x_5);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___elambda__5), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___elambda__4___boxed), 3, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_box(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___elambda__3___boxed), 6, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_4);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___elambda__2), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_box(x_3);
x_12 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___elambda__1___boxed), 6, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_chainLeft___elambda__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_IO_FS_Stream_chainLeft___elambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_chainLeft___elambda__3___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_IO_FS_Stream_chainLeft___elambda__3(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_chainLeft___elambda__4(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_IO_FS_Stream_chainLeft(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_string_append(x_2, x_3);
x_7 = lean_apply_2(x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_apply_2(x_5, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_8, x_3, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box_usize(x_2);
x_6 = lean_apply_2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___elambda__5), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___elambda__4___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___elambda__3), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___elambda__2), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___elambda__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_withPrefix___elambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_withPrefix___elambda__4(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta___closed__2;
x_2 = l_Lean_Server_instInhabitedDocumentMeta___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Server_instInhabitedDocumentMeta___closed__3;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_System_Uri_fileUriToPath_x3f(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_6);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_extract(x_8, x_9, x_5);
lean_dec(x_5);
x_11 = lean_string_utf8_byte_size(x_8);
x_12 = lean_string_utf8_extract(x_8, x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_13 = lean_string_append(x_10, x_3);
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_FileMap_ofString(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_replaceLspRange(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_maybeTee___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_SERVER_LOG_DIR", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Server_maybeTee___closed__1;
x_6 = lean_io_getenv(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l_IO_FS_createDirAll(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_System_mkFilePath(x_18);
x_20 = 1;
x_21 = lean_io_prim_handle_mk(x_19, x_20, x_15);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_stream_of_handle(x_23);
if (x_2 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = l_IO_FS_Stream_chainRight(x_3, x_24, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = 1;
x_28 = l_IO_FS_Stream_chainLeft(x_24, x_3, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_stream_of_handle(x_29);
if (x_2 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 1;
x_33 = l_IO_FS_Stream_chainRight(x_3, x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 1;
x_36 = l_IO_FS_Stream_chainLeft(x_31, x_3, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Server_maybeTee(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Server_replaceLspRange(x_1, x_3, x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_FileMap_ofString(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_applyDocumentChange(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_foldDocumentChanges___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Server_applyDocumentChange(x_4, x_6);
lean_dec(x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Server_foldDocumentChanges___spec__1(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_foldDocumentChanges___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Server_foldDocumentChanges___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_foldDocumentChanges(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected structured object, got '", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Diagnostics_0__Lean_Lsp_toJsonPublishDiagnosticsParams____x40_Lean_Data_Lsp_Diagnostics___hyg_1730_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_publishDiagnostics___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2(x_5);
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
static lean_object* _init_l_Lean_Server_publishDiagnostics___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/publishDiagnostics", 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_publishDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_2);
x_10 = l_Lean_Server_publishDiagnostics___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_publishDiagnostics___spec__1(x_3, x_11, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_publishProgress___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonLeanFileProgressParams____x40_Lean_Data_Lsp_Extra___hyg_927_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_publishProgress___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_publishProgress___spec__2(x_5);
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
static lean_object* _init_l_Lean_Server_publishProgress___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/fileProgress", 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_publishProgress(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Server_publishProgress___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_publishProgress___spec__1(x_3, x_11, x_4);
return x_12;
}
}
static lean_object* _init_l_Lean_Server_publishProgressAtPos___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_publishProgressAtPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Lean_FileMap_utf8PosToLspPos(x_6, x_2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_string_utf8_byte_size(x_8);
lean_dec(x_8);
x_10 = l_Lean_FileMap_utf8PosToLspPos(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_4);
x_13 = l_Lean_Server_publishProgressAtPos___closed__1;
x_14 = lean_array_push(x_13, x_12);
x_15 = l_Lean_Server_publishProgress(x_1, x_14, x_3, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_publishProgressAtPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Server_publishProgressAtPos(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_publishProgressDone(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_instInhabitedDocumentMeta___closed__1;
x_5 = l_Lean_Server_publishProgress(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_applyWorkspaceEdit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonApplyWorkspaceEditParams____x40_Lean_Data_Lsp_Basic___hyg_4575_(x_1);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_applyWorkspaceEdit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_applyWorkspaceEdit___spec__2(x_6);
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
static lean_object* _init_l_Lean_Server_applyWorkspaceEdit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspace/applyEdit", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_applyWorkspaceEdit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_applyWorkspaceEdit___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyWorkspaceEdit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Server_applyWorkspaceEdit___closed__2;
x_5 = l_Lean_Server_applyWorkspaceEdit___closed__1;
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
x_7 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_applyWorkspaceEdit___spec__1(x_2, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Range_toLspRange(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Range_toLspRange___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Range_toLspRange(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_TextSync(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
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
res = initialize_Lean_Data_Lsp_TextSync(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedDocumentMeta___closed__1 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__1();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__1);
l_Lean_Server_instInhabitedDocumentMeta___closed__2 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__2();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__2);
l_Lean_Server_instInhabitedDocumentMeta___closed__3 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__3();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__3);
l_Lean_Server_instInhabitedDocumentMeta___closed__4 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__4();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__4);
l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
l_Lean_Server_maybeTee___closed__1 = _init_l_Lean_Server_maybeTee___closed__1();
lean_mark_persistent(l_Lean_Server_maybeTee___closed__1);
l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__1 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__1();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__1);
l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__2 = _init_l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__2();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at_Lean_Server_publishDiagnostics___spec__2___closed__2);
l_Lean_Server_publishDiagnostics___closed__1 = _init_l_Lean_Server_publishDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Server_publishDiagnostics___closed__1);
l_Lean_Server_publishProgress___closed__1 = _init_l_Lean_Server_publishProgress___closed__1();
lean_mark_persistent(l_Lean_Server_publishProgress___closed__1);
l_Lean_Server_publishProgressAtPos___closed__1 = _init_l_Lean_Server_publishProgressAtPos___closed__1();
lean_mark_persistent(l_Lean_Server_publishProgressAtPos___closed__1);
l_Lean_Server_applyWorkspaceEdit___closed__1 = _init_l_Lean_Server_applyWorkspaceEdit___closed__1();
lean_mark_persistent(l_Lean_Server_applyWorkspaceEdit___closed__1);
l_Lean_Server_applyWorkspaceEdit___closed__2 = _init_l_Lean_Server_applyWorkspaceEdit___closed__2();
lean_mark_persistent(l_Lean_Server_applyWorkspaceEdit___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

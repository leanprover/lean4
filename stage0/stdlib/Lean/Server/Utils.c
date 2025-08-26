// Lean compiler output
// Module: Lean.Server.Utils
// Imports: Init.System.Uri Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Lean.Data.Lsp.TextSync Lean.Server.InfoUtils
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0(lean_object*, lean_object*, uint8_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object*);
static lean_object* l_Lean_Server_maybeTee___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_System_Uri_pathToUri(lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
static lean_object* l_Lean_Server_documentUriFromModule_x3f___closed__0;
lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_Server_moduleFromDocumentUri_spec__0(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Server_mkPublishDiagnosticsNotification___closed__0;
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkFileProgressNotification___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta;
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__0;
lean_object* l_Lean_getSrcSearchPath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
static lean_object* l_Lean_Server_mkFileProgressDoneNotification___closed__0;
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_moduleFromDocumentUri___closed__0;
LEAN_EXPORT lean_object* l_String_Range_toLspRange(lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0;
LEAN_EXPORT lean_object* l_IO_throwServerError(lean_object*, lean_object*, lean_object*);
lean_object* l_System_mkFilePath(lean_object*);
lean_object* l_String_toFileMap(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkFileProgressAtPosNotification___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft(lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_foldDocumentChanges_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_throwServerError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_throwServerError___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_usize(x_4);
x_7 = lean_apply_2(x_1, x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
lean_inc(x_8);
x_12 = lean_apply_2(x_11, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
if (x_3 == 0)
{
uint8_t x_13; 
lean_dec_ref(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = lean_apply_1(x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
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
}
else
{
uint8_t x_27; 
lean_dec_ref(x_10);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_dec_ref(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
lean_inc(x_6);
x_10 = lean_apply_2(x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
if (x_3 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec_ref(x_10);
x_16 = lean_apply_1(x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
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
lean_dec_ref(x_8);
lean_dec(x_6);
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
else
{
lean_dec_ref(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = lean_apply_1(x_6, x_5);
return x_7;
}
else
{
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_box(x_3);
lean_inc_ref(x_2);
x_9 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__0___boxed), 5, 3);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_box(x_3);
lean_inc_ref(x_2);
x_11 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__1___boxed), 4, 3);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__2), 3, 2);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_2);
lean_ctor_set(x_1, 3, x_11);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_19 = lean_box(x_3);
lean_inc_ref(x_2);
x_20 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__0___boxed), 5, 3);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_box(x_3);
lean_inc_ref(x_2);
x_22 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__1___boxed), 4, 3);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_21);
x_23 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__2), 3, 2);
lean_closure_set(x_23, 0, x_13);
lean_closure_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_17);
lean_ctor_set(x_24, 5, x_18);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_IO_FS_Stream_chainRight___lam__0(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_IO_FS_Stream_chainRight___lam__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_IO_FS_Stream_chainRight(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_5);
x_7 = lean_apply_2(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
if (x_2 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_3, x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_apply_1(x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_2(x_3, x_5, x_12);
return x_13;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_11;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_5);
x_7 = lean_apply_2(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
if (x_2 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_3, x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_apply_1(x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_2(x_3, x_5, x_12);
return x_13;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_11;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_4);
x_11 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
x_12 = lean_box(x_3);
lean_inc_ref(x_4);
x_13 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__1___boxed), 6, 4);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_box(x_3);
x_15 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__2___boxed), 6, 4);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_4);
lean_ctor_set(x_2, 4, x_15);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
x_20 = lean_ctor_get(x_2, 4);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
lean_inc_ref(x_4);
x_22 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__0), 3, 2);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_16);
x_23 = lean_box(x_3);
lean_inc_ref(x_4);
x_24 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__1___boxed), 6, 4);
lean_closure_set(x_24, 0, x_5);
lean_closure_set(x_24, 1, x_23);
lean_closure_set(x_24, 2, x_18);
lean_closure_set(x_24, 3, x_4);
x_25 = lean_box(x_3);
x_26 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__2___boxed), 6, 4);
lean_closure_set(x_26, 0, x_6);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_20);
lean_closure_set(x_26, 3, x_4);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_19);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_21);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_IO_FS_Stream_chainLeft___lam__1(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_IO_FS_Stream_chainLeft___lam__2(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_IO_FS_Stream_chainLeft(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_2(x_3, x_4, x_7);
return x_8;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_string_append(x_1, x_3);
x_6 = lean_apply_2(x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_2);
lean_inc_ref(x_5);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___lam__0), 5, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___lam__1___boxed), 4, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_ctor_set(x_1, 4, x_7);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc_ref(x_2);
lean_inc_ref(x_12);
x_14 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___lam__0), 5, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_10);
x_15 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___lam__1___boxed), 4, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_11);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_withPrefix___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta___closed__1;
x_2 = l_Lean_Server_instInhabitedDocumentMeta___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_Server_instInhabitedDocumentMeta___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Lean_Server_instInhabitedDocumentMeta___closed__0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_9 = l_System_Uri_fileUriToPath_x3f(x_3);
if (lean_obj_tag(x_9) == 0)
{
x_5 = x_3;
goto block_8;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_5 = x_10;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_byte_size(x_4);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_4);
x_8 = l_Lean_FileMap_lspPosToUtf8Pos(x_1, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_extract(x_6, x_9, x_7);
lean_dec(x_7);
x_11 = lean_string_utf8_byte_size(x_6);
x_12 = lean_string_utf8_extract(x_6, x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_13 = l_String_crlfToLf(x_3);
x_14 = lean_string_append(x_10, x_13);
lean_dec_ref(x_13);
x_15 = lean_string_append(x_14, x_12);
lean_dec_ref(x_12);
x_16 = l_String_toFileMap(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_replaceLspRange(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_maybeTee___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SERVER_LOG_DIR", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_maybeTee(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Server_maybeTee___closed__0;
x_6 = lean_io_getenv(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec_ref(x_1);
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
lean_dec_ref(x_6);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec_ref(x_7);
x_14 = l_IO_FS_createDirAll(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
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
lean_dec_ref(x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_stream_of_handle(x_23);
x_25 = 1;
if (x_2 == 0)
{
lean_object* x_26; 
x_26 = l_IO_FS_Stream_chainRight(x_3, x_24, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; 
x_27 = l_IO_FS_Stream_chainLeft(x_24, x_3, x_25);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_stream_of_handle(x_28);
x_31 = 1;
if (x_2 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_IO_FS_Stream_chainRight(x_3, x_30, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_IO_FS_Stream_chainLeft(x_30, x_3, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_3);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Server_replaceLspRange(x_1, x_3, x_4);
lean_dec_ref(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l_String_crlfToLf(x_6);
lean_dec_ref(x_6);
x_8 = l_String_toFileMap(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_applyDocumentChange(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_foldDocumentChanges_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Server_applyDocumentChange(x_4, x_6);
lean_dec_ref(x_4);
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
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_foldDocumentChanges_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_foldDocumentChanges_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_foldDocumentChanges(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_mkPublishDiagnosticsNotification___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("textDocument/publishDiagnostics", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Server_mkPublishDiagnosticsNotification___closed__0;
x_6 = lean_nat_to_int(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Server_mkFileProgressNotification___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("$/lean/fileProgress", 19, 19);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Server_mkFileProgressNotification___closed__0;
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_mkFileProgressNotification(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_mkFileProgressAtPosNotification___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_4);
x_6 = l_Lean_FileMap_utf8PosToLspPos(x_4, x_2);
x_7 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_4);
x_8 = l_Lean_FileMap_utf8PosToLspPos(x_4, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_3);
x_11 = l_Lean_Server_mkFileProgressAtPosNotification___closed__0;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_Server_mkFileProgressNotification(x_1, x_12);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Server_mkFileProgressAtPosNotification(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_mkFileProgressDoneNotification___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_mkFileProgressDoneNotification___closed__0;
x_3 = l_Lean_Server_mkFileProgressNotification(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_mkFileProgressDoneNotification(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workspace/applyEdit", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0;
x_3 = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("external:", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
x_4 = lean_string_append(x_3, x_1);
x_5 = l_Lean_Name_str___override(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
x_5 = l_String_dropPrefix_x3f(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_string_utf8_extract(x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_string_utf8_extract(x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec_ref(x_1);
x_19 = lean_box(0);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_box(0);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Server_documentUriFromModule_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_getSrcSearchPath(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Server_documentUriFromModule_x3f___closed__0;
x_8 = l_Lean_SearchPath_findModuleWithExt(x_5, x_7, x_1, x_6);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec_ref(x_8);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_io_realpath(x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_System_Uri_pathToUri(x_19);
lean_ctor_set(x_9, 0, x_20);
lean_ctor_set(x_17, 0, x_9);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l_System_Uri_pathToUri(x_21);
lean_ctor_set(x_9, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_9);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = lean_io_realpath(x_29, x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = l_System_Uri_pathToUri(x_31);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_39 = x_30;
} else {
 lean_dec_ref(x_30);
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
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
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
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
return x_4;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_2);
return x_49;
}
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_Server_moduleFromDocumentUri_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Server_moduleFromDocumentUri___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_documentUriFromModule_x3f___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_System_Uri_fileUriToPath_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
lean_inc(x_6);
x_7 = l_System_FilePath_extension(x_6);
x_8 = l_Lean_Server_moduleFromDocumentUri___closed__0;
x_9 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_Server_moduleFromDocumentUri_spec__0(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_getSrcSearchPath(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_searchModuleNameOfFileName(x_6, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_dec_ref(x_1);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec_ref(x_16);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec_ref(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_Server_moduleFromDocumentUri_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Range_toLspRange(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_6 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_4);
lean_dec(x_4);
x_7 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_5);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc_ref(x_1);
x_10 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_FileMap_utf8PosToLspPos(x_1, x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* initialize_Init_System_Uri(uint8_t builtin, lean_object*);
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
res = initialize_Init_System_Uri(builtin, lean_io_mk_world());
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
l_Lean_Server_instInhabitedDocumentMeta___closed__0 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__0();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__0);
l_Lean_Server_instInhabitedDocumentMeta___closed__1 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__1();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__1);
l_Lean_Server_instInhabitedDocumentMeta___closed__2 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__2();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__2);
l_Lean_Server_instInhabitedDocumentMeta___closed__3 = _init_l_Lean_Server_instInhabitedDocumentMeta___closed__3();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta___closed__3);
l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
l_Lean_Server_maybeTee___closed__0 = _init_l_Lean_Server_maybeTee___closed__0();
lean_mark_persistent(l_Lean_Server_maybeTee___closed__0);
l_Lean_Server_mkPublishDiagnosticsNotification___closed__0 = _init_l_Lean_Server_mkPublishDiagnosticsNotification___closed__0();
lean_mark_persistent(l_Lean_Server_mkPublishDiagnosticsNotification___closed__0);
l_Lean_Server_mkFileProgressNotification___closed__0 = _init_l_Lean_Server_mkFileProgressNotification___closed__0();
lean_mark_persistent(l_Lean_Server_mkFileProgressNotification___closed__0);
l_Lean_Server_mkFileProgressAtPosNotification___closed__0 = _init_l_Lean_Server_mkFileProgressAtPosNotification___closed__0();
lean_mark_persistent(l_Lean_Server_mkFileProgressAtPosNotification___closed__0);
l_Lean_Server_mkFileProgressDoneNotification___closed__0 = _init_l_Lean_Server_mkFileProgressDoneNotification___closed__0();
lean_mark_persistent(l_Lean_Server_mkFileProgressDoneNotification___closed__0);
l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0 = _init_l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0();
lean_mark_persistent(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0);
l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1 = _init_l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1();
lean_mark_persistent(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1);
l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0 = _init_l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0();
lean_mark_persistent(l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0);
l_Lean_Server_documentUriFromModule_x3f___closed__0 = _init_l_Lean_Server_documentUriFromModule_x3f___closed__0();
lean_mark_persistent(l_Lean_Server_documentUriFromModule_x3f___closed__0);
l_Lean_Server_moduleFromDocumentUri___closed__0 = _init_l_Lean_Server_moduleFromDocumentUri___closed__0();
lean_mark_persistent(l_Lean_Server_moduleFromDocumentUri___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

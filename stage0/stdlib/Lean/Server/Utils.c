// Lean compiler output
// Module: Lean.Server.Utils
// Imports: public import Init.System.Uri public import Lean.Data.Lsp.Communication public import Lean.Data.Lsp.Diagnostics public import Lean.Data.Lsp.Extra public import Lean.Server.InfoUtils
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta_default___closed__1;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0(lean_object*, lean_object*, uint8_t, size_t);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object*);
static lean_object* l_Lean_Server_instInhabitedDocumentMeta_default___closed__0;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_Uri_pathToUri(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object*, lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
static lean_object* l_Lean_Server_documentUriFromModule_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta_default;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Server_mkPublishDiagnosticsNotification___closed__0;
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkFileProgressNotification___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta;
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkFileProgressDoneNotification___closed__0;
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_moduleFromDocumentUri___closed__0;
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0;
LEAN_EXPORT lean_object* l_IO_throwServerError(lean_object*, lean_object*);
lean_object* l_String_toFileMap(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
static lean_object* l_Lean_Server_mkFileProgressAtPosNotification___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___redArg___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
static lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft(lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_throwServerError___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_throwServerError___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_throwServerError___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_throwServerError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_throwServerError___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_throwServerError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_throwServerError(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, size_t x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_usize(x_4);
x_7 = lean_apply_2(x_1, x_6, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_10);
lean_dec_ref(x_2);
lean_inc(x_8);
x_11 = lean_apply_2(x_10, x_8, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
if (x_3 == 0)
{
lean_dec_ref(x_9);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_14; 
lean_free_object(x_11);
x_14 = lean_apply_1(x_9, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
else
{
lean_dec(x_11);
if (x_3 == 0)
{
lean_object* x_21; 
lean_dec_ref(x_9);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_8);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_apply_1(x_9, lean_box(0));
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_23 = x_22;
} else {
 lean_dec_ref(x_22);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec_ref(x_9);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_IO_FS_Stream_chainRight___lam__0(x_1, x_2, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
lean_inc(x_6);
x_9 = lean_apply_2(x_8, x_6, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
if (x_3 == 0)
{
lean_dec_ref(x_7);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
else
{
lean_object* x_12; 
lean_free_object(x_9);
x_12 = lean_apply_1(x_7, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
else
{
lean_dec(x_9);
if (x_3 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_7);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_apply_1(x_7, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_21 = x_20;
} else {
 lean_dec_ref(x_20);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec_ref(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_IO_FS_Stream_chainRight___lam__1(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_5, lean_box(0));
return x_6;
}
else
{
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_chainRight___lam__2(x_1, x_2);
return x_4;
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
x_12 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__2___boxed), 3, 2);
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
x_23 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainRight___lam__2___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_IO_FS_Stream_chainRight(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_4);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
else
{
lean_dec_ref(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_chainLeft___lam__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_5);
x_7 = lean_apply_2(x_1, x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_7);
if (x_2 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = lean_apply_2(x_3, x_5, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_1(x_4, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
x_10 = lean_apply_2(x_3, x_5, lean_box(0));
return x_10;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_9;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_IO_FS_Stream_chainLeft___lam__1(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_5);
x_7 = lean_apply_2(x_1, x_5, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
lean_dec_ref(x_7);
if (x_2 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_4);
x_8 = lean_apply_2(x_3, x_5, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_apply_1(x_4, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
x_10 = lean_apply_2(x_3, x_5, lean_box(0));
return x_10;
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_9;
}
}
}
else
{
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_IO_FS_Stream_chainLeft___lam__2(x_1, x_7, x_3, x_4, x_5);
return x_8;
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
x_11 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__0___boxed), 3, 2);
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
x_22 = lean_alloc_closure((void*)(l_IO_FS_Stream_chainLeft___lam__0___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l_IO_FS_Stream_chainLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_IO_FS_Stream_chainLeft(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_6);
x_7 = lean_apply_2(x_3, x_4, lean_box(0));
return x_7;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_withPrefix___lam__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_string_append(x_1, x_3);
x_6 = lean_apply_2(x_2, x_5, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_withPrefix___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
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
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___lam__0___boxed), 5, 3);
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
x_14 = lean_alloc_closure((void*)(l_IO_FS_Stream_withPrefix___lam__0___boxed), 5, 3);
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
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_instInhabitedFileMap_default;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Lean_Server_instInhabitedDocumentMeta_default___closed__0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_instInhabitedDocumentMeta_default;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
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
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(x_1, x_10, x_11, x_2);
return x_12;
}
}
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object* x_1) {
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
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0;
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_memcmp(x_1, x_2, x_7, x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_3);
x_11 = l_String_Slice_pos_x21(x_10, x_4);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_String_Slice_toString(x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_String_Slice_toString(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l_Lean_getSrcSearchPath();
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Server_documentUriFromModule_x3f___closed__0;
x_8 = l_Lean_SearchPath_findModuleWithExt(x_6, x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
lean_free_object(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_io_realpath(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_System_Uri_pathToUri(x_15);
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_System_Uri_pathToUri(x_17);
lean_ctor_set(x_10, 0, x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_10);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_io_realpath(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = l_System_Uri_pathToUri(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_10);
x_33 = lean_box(0);
lean_ctor_set(x_8, 0, x_33);
return x_8;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_io_realpath(x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = l_System_Uri_pathToUri(x_38);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_34);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_8, 0);
lean_inc(x_49);
lean_dec(x_8);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_5);
if (x_51 == 0)
{
return x_5;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
lean_dec(x_5);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_documentUriFromModule_x3f(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_System_Uri_fileUriToPath_x3f(x_1);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_System_FilePath_extension(x_5);
x_7 = l_Lean_Server_moduleFromDocumentUri___closed__0;
x_8 = l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; 
lean_free_object(x_3);
x_10 = l_Lean_getSrcSearchPath();
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_searchModuleNameOfFileName(x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; 
lean_dec(x_14);
x_16 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
x_20 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
lean_inc(x_28);
x_29 = l_System_FilePath_extension(x_28);
x_30 = l_Lean_Server_moduleFromDocumentUri___closed__0;
x_31 = l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_32 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_getSrcSearchPath();
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_searchModuleNameOfFileName(x_28, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec_ref(x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_41 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_28);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_47 = x_34;
} else {
 lean_dec_ref(x_34);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
x_49 = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(x_1);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_moduleFromDocumentUri(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_toLspRange(lean_object* x_1, lean_object* x_2) {
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
lean_object* initialize_Init_System_Uri(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedDocumentMeta_default___closed__0 = _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__0();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default___closed__0);
l_Lean_Server_instInhabitedDocumentMeta_default___closed__1 = _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default___closed__1);
l_Lean_Server_instInhabitedDocumentMeta_default = _init_l_Lean_Server_instInhabitedDocumentMeta_default();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default);
l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
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
l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0 = _init_l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0();
lean_mark_persistent(l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0);
l_Lean_Server_documentUriFromModule_x3f___closed__0 = _init_l_Lean_Server_documentUriFromModule_x3f___closed__0();
lean_mark_persistent(l_Lean_Server_documentUriFromModule_x3f___closed__0);
l_Lean_Server_moduleFromDocumentUri___closed__0 = _init_l_Lean_Server_moduleFromDocumentUri___closed__0();
lean_mark_persistent(l_Lean_Server_moduleFromDocumentUri___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

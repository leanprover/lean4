// Lean compiler output
// Module: Lean.Data.Lsp.Capabilities
// Imports: Init Lean.Data.JsonRpc Lean.Data.Lsp.TextSync
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
lean_object* l_Lean_Lsp_ClientCapabilities_hasFromJson___boxed(lean_object*);
lean_object* l_Lean_Lsp_ClientCapabilities_hasFromJson(lean_object*);
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__6;
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__2;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_Lsp_ServerCapabilities_hasToJson___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_ServerCapabilities_hasToJson___closed__2;
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__7;
lean_object* l_Lean_Lsp_ServerCapabilities_hasToJson___boxed(lean_object*);
lean_object* l_Lean_Lsp_ServerCapabilities_hasToJson___closed__1;
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__1;
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__3;
lean_object* l_Lean_Lsp_ServerCapabilities_hasToJson(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_Lsp_ServerCapabilities_hasToJson___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_Lsp_TextDocumentSyncOptions_hasToJson___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__4;
extern lean_object* l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__8;
lean_object* l_Lean_Lsp_ClientCapabilities_hasFromJson___closed__1;
lean_object* _init_l_Lean_Lsp_ClientCapabilities_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_ClientCapabilities_hasFromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_ClientCapabilities_hasFromJson___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lsp_ClientCapabilities_hasFromJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_ClientCapabilities_hasFromJson(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_opt___at_Lean_Lsp_ServerCapabilities_hasToJson___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_9 = lean_ctor_get(x_4, 0);
x_10 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__1;
x_11 = l_Lean_Json_opt___at_Lean_Lsp_TextDocumentSyncOptions_hasToJson___spec__1(x_10, x_9);
x_12 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_5);
x_13 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_15, 0, x_7);
x_16 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_8);
x_19 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__4;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
switch (x_6) {
case 0:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__6;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_List_append___rarg(x_11, x_26);
x_28 = l_Lean_Json_mkObj(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__7;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_append___rarg(x_11, x_33);
x_35 = l_Lean_Json_mkObj(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
return x_37;
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l_Lean_Lsp_TextDocumentSyncOptions_hasToJson___closed__8;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_List_append___rarg(x_11, x_40);
x_42 = l_Lean_Json_mkObj(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_21);
return x_44;
}
}
}
}
}
lean_object* _init_l_Lean_Lsp_ServerCapabilities_hasToJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocumentSync");
return x_1;
}
}
lean_object* _init_l_Lean_Lsp_ServerCapabilities_hasToJson___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hoverProvider");
return x_1;
}
}
lean_object* l_Lean_Lsp_ServerCapabilities_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Lsp_ServerCapabilities_hasToJson___closed__1;
x_4 = l_Lean_Json_opt___at_Lean_Lsp_ServerCapabilities_hasToJson___spec__1(x_3, x_2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_6 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_6, 0, x_5);
x_7 = l_Lean_Lsp_ServerCapabilities_hasToJson___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_List_append___rarg(x_4, x_10);
x_12 = l_Lean_Json_mkObj(x_11);
return x_12;
}
}
lean_object* l_Lean_Json_opt___at_Lean_Lsp_ServerCapabilities_hasToJson___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_Lsp_ServerCapabilities_hasToJson___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Lsp_ServerCapabilities_hasToJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_ServerCapabilities_hasToJson(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(lean_object*);
lean_object* initialize_Lean_Data_Lsp_TextSync(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_Capabilities(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_TextSync(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_ClientCapabilities_hasFromJson___closed__1 = _init_l_Lean_Lsp_ClientCapabilities_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_Lsp_ClientCapabilities_hasFromJson___closed__1);
l_Lean_Lsp_ServerCapabilities_hasToJson___closed__1 = _init_l_Lean_Lsp_ServerCapabilities_hasToJson___closed__1();
lean_mark_persistent(l_Lean_Lsp_ServerCapabilities_hasToJson___closed__1);
l_Lean_Lsp_ServerCapabilities_hasToJson___closed__2 = _init_l_Lean_Lsp_ServerCapabilities_hasToJson___closed__2();
lean_mark_persistent(l_Lean_Lsp_ServerCapabilities_hasToJson___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

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
extern lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__3;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_change___closed__1;
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities(lean_object*);
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson(lean_object*);
uint8_t l_Lean_Lsp_ServerCapabilities_hoverProvider___default;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonServerCapabilities___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentSyncOptions___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1;
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson___boxed(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities(lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerCapabilities(lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerCapabilities___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonServerCapabilities___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_Lsp_instToJsonServerCapabilities___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__3;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_ServerCapabilities_textDocumentSync_x3f___default;
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities___closed__1;
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonSaveOptions___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_Lsp_instToJsonTextDocumentSyncOptions___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__2;
extern lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__1;
extern lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__1;
extern lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__4;
lean_object* l_Lean_Json_opt___at_Lean_Lsp_instToJsonServerCapabilities___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__2;
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities___closed__2;
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___closed__1;
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___boxed(lean_object*);
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonClientCapabilities___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonClientCapabilities(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_ClientCapabilities_hasToJson(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_ServerCapabilities_textDocumentSync_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_Lsp_ServerCapabilities_hoverProvider___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonServerCapabilities___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__1;
x_5 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonSaveOptions___spec__1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Parser_Tactic_change___closed__1;
x_9 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___spec__1(x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__2;
x_13 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonSaveOptions___spec__1(x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__3;
x_17 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonSaveOptions___spec__1(x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_box(0);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__4;
x_22 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentSyncOptions___spec__1(x_3, x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unbox(x_7);
lean_dec(x_7);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 1, x_25);
x_26 = lean_unbox(x_15);
lean_dec(x_15);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 2, x_26);
x_27 = lean_unbox(x_20);
lean_dec(x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*1 + 3, x_27);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__4;
x_30 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentSyncOptions___spec__1(x_3, x_29);
lean_dec(x_3);
x_31 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_unbox(x_7);
lean_dec(x_7);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_31, sizeof(void*)*1 + 1, x_33);
x_34 = lean_unbox(x_15);
lean_dec(x_15);
lean_ctor_set_uint8(x_31, sizeof(void*)*1 + 2, x_34);
x_35 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*1 + 3, x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
return x_36;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocumentSync");
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hoverProvider");
return x_1;
}
}
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Lsp_instFromJsonServerCapabilities___closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonServerCapabilities___spec__1(x_1, x_2);
x_4 = l_Lean_Lsp_instFromJsonServerCapabilities___closed__2;
x_5 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonSaveOptions___spec__1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_3);
x_10 = lean_unbox(x_8);
lean_dec(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonServerCapabilities___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonServerCapabilities___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonServerCapabilities(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_opt___at_Lean_Lsp_instToJsonServerCapabilities___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 2);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 3);
x_12 = lean_ctor_get(x_7, 0);
x_13 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__4;
x_14 = l_Lean_Json_opt___at_Lean_Lsp_instToJsonTextDocumentSyncOptions___spec__1(x_13, x_12);
x_15 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_15, 0, x_8);
x_16 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_10);
x_19 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__2;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_21, 0, x_11);
x_22 = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__3;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
switch (x_9) {
case 0:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_List_append___rarg(x_14, x_28);
x_30 = l_Lean_Json_mkObj(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_List_append___rarg(x_14, x_35);
x_37 = l_Lean_Json_mkObj(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__3;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_25);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_List_append___rarg(x_14, x_42);
x_44 = l_Lean_Json_mkObj(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
}
}
}
}
lean_object* l_Lean_Lsp_instToJsonServerCapabilities(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Lsp_instFromJsonServerCapabilities___closed__1;
x_4 = l_Lean_Json_opt___at_Lean_Lsp_instToJsonServerCapabilities___spec__1(x_3, x_2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_6 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_6, 0, x_5);
x_7 = l_Lean_Lsp_instFromJsonServerCapabilities___closed__2;
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
lean_object* l_Lean_Json_opt___at_Lean_Lsp_instToJsonServerCapabilities___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at_Lean_Lsp_instToJsonServerCapabilities___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Lsp_instToJsonServerCapabilities___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonServerCapabilities(x_1);
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
l_Lean_Lsp_instFromJsonClientCapabilities___closed__1 = _init_l_Lean_Lsp_instFromJsonClientCapabilities___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonClientCapabilities___closed__1);
l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1 = _init_l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1();
lean_mark_persistent(l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1);
l_Lean_Lsp_ServerCapabilities_textDocumentSync_x3f___default = _init_l_Lean_Lsp_ServerCapabilities_textDocumentSync_x3f___default();
lean_mark_persistent(l_Lean_Lsp_ServerCapabilities_textDocumentSync_x3f___default);
l_Lean_Lsp_ServerCapabilities_hoverProvider___default = _init_l_Lean_Lsp_ServerCapabilities_hoverProvider___default();
l_Lean_Lsp_instFromJsonServerCapabilities___closed__1 = _init_l_Lean_Lsp_instFromJsonServerCapabilities___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonServerCapabilities___closed__1);
l_Lean_Lsp_instFromJsonServerCapabilities___closed__2 = _init_l_Lean_Lsp_instFromJsonServerCapabilities___closed__2();
lean_mark_persistent(l_Lean_Lsp_instFromJsonServerCapabilities___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

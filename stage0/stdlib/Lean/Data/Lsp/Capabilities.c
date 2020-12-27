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
extern lean_object* l_Lean_instFromJsonOption___rarg___closed__1;
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__3;
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities;
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson(lean_object*);
uint8_t l_Lean_Lsp_ServerCapabilities_hoverProvider___default;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonTextDocumentSyncOptions____x40_Lean_Data_Lsp_TextSync___hyg_419_(lean_object*);
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson___closed__1;
lean_object* l_Lean_Lsp_ClientCapabilities_hasToJson___boxed(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities(lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerCapabilities;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonSaveOptions____x40_Lean_Data_Lsp_TextSync___hyg_335____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61_(lean_object*);
lean_object* l_Lean_Lsp_instToJsonServerCapabilities___closed__1;
lean_object* l_Lean_Lsp_ServerCapabilities_textDocumentSync_x3f___default;
lean_object* l_Lean_Lsp_instFromJsonServerCapabilities___closed__1;
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonTextDocumentSyncOptions____x40_Lean_Data_Lsp_TextSync___hyg_463_(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___closed__1;
lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____spec__1___boxed(lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hoverProvider");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocumentSync");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_4, 0, x_3);
x_5 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Json_mkObj(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonTextDocumentSyncOptions____x40_Lean_Data_Lsp_TextSync___hyg_419_(x_12);
x_14 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
}
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonServerCapabilities___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonServerCapabilities() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonServerCapabilities___closed__1;
return x_1;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_instFromJsonOption___rarg___closed__1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonTextDocumentSyncOptions____x40_Lean_Data_Lsp_TextSync___hyg_463_(x_3);
lean_dec(x_3);
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
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonSaveOptions____x40_Lean_Data_Lsp_TextSync___hyg_335____spec__1(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_unbox(x_10);
lean_dec(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_5);
x_15 = lean_unbox(x_13);
lean_dec(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_fromJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_61____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonServerCapabilities___closed__1;
return x_1;
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
l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1 = _init_l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__1);
l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2 = _init_l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__2);
l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__3 = _init_l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Capabilities_0__Lean_Lsp_toJsonServerCapabilities____x40_Lean_Data_Lsp_Capabilities___hyg_35____closed__3);
l_Lean_Lsp_instToJsonServerCapabilities___closed__1 = _init_l_Lean_Lsp_instToJsonServerCapabilities___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonServerCapabilities___closed__1);
l_Lean_Lsp_instToJsonServerCapabilities = _init_l_Lean_Lsp_instToJsonServerCapabilities();
lean_mark_persistent(l_Lean_Lsp_instToJsonServerCapabilities);
l_Lean_Lsp_instFromJsonServerCapabilities___closed__1 = _init_l_Lean_Lsp_instFromJsonServerCapabilities___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonServerCapabilities___closed__1);
l_Lean_Lsp_instFromJsonServerCapabilities = _init_l_Lean_Lsp_instFromJsonServerCapabilities();
lean_mark_persistent(l_Lean_Lsp_instFromJsonServerCapabilities);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

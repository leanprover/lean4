// Lean compiler output
// Module: Lean.Data.Lsp.Extra
// Imports: Init Lean.Data.Json Lean.Data.JsonRpc Lean.Data.Lsp.Basic
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
extern lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_976____closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_533____spec__1(lean_object*, lean_object*);
lean_object* l_List_join___rarg(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_8_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42_(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams;
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1;
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__1;
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___boxed(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1;
extern lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_499____closed__1;
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics(lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___boxed(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__1;
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42____boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_219____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_8_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_499____closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_JsonNumber_fromNat(x_3);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_976____closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_List_join___rarg(x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_8_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_499____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_533____spec__1(x_1, x_2);
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
x_6 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonVersionedTextDocumentIdentifier____x40_Lean_Data_Lsp_Basic___hyg_976____closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonPosition____x40_Lean_Data_Lsp_Basic___hyg_219____spec__1(x_1, x_6);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParams____x40_Lean_Data_Lsp_Extra___hyg_42____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonWaitForDiagnostics(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Json_mkObj(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1;
return x_2;
}
}
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instToJsonWaitForDiagnostics(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_Extra(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__1 = _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonWaitForDiagnosticsParams___closed__1);
l_Lean_Lsp_instToJsonWaitForDiagnosticsParams = _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParams();
lean_mark_persistent(l_Lean_Lsp_instToJsonWaitForDiagnosticsParams);
l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__1 = _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams___closed__1);
l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams = _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParams);
l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1 = _init_l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1);
l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1 = _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

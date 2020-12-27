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
extern lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__1;
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParam___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_484____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnosticsParam;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_27_(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1;
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam;
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnostics___boxed(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1;
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_27____boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_7_(lean_object*);
lean_object* l_Lean_Lsp_instToJsonWaitForDiagnostics___boxed(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam___closed__1;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_7_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonWaitForDiagnosticsParam___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_27_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_484____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_27____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_27_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_27____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam___closed__1;
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
l_Lean_Lsp_instToJsonWaitForDiagnosticsParam___closed__1 = _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParam___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonWaitForDiagnosticsParam___closed__1);
l_Lean_Lsp_instToJsonWaitForDiagnosticsParam = _init_l_Lean_Lsp_instToJsonWaitForDiagnosticsParam();
lean_mark_persistent(l_Lean_Lsp_instToJsonWaitForDiagnosticsParam);
l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam___closed__1 = _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam___closed__1);
l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam = _init_l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWaitForDiagnosticsParam);
l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1 = _init_l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWaitForDiagnostics___closed__1);
l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1 = _init_l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonWaitForDiagnostics___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

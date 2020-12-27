// Lean compiler output
// Module: Lean.Data.Lsp.Hover
// Imports: Init Lean.Data.Json Lean.Data.Lsp.Basic
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
lean_object* l_Lean_Lsp_instToJsonHoverParams(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1109_(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHoverParams___boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1;
lean_object* l_Lean_Lsp_instToJsonHover___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____boxed(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__2;
extern lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__2;
lean_object* l_Lean_Lsp_Hover_range_x3f___default;
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11_(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocationLink____x40_Lean_Data_Lsp_Basic___hyg_565____spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1083_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_1438_(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHoverParams(lean_object*);
lean_object* l_Lean_Lsp_instToJsonHover;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_1412_(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__3;
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_328_(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHover;
lean_object* l_Lean_Lsp_instFromJsonHover___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____spec__1(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Lsp_Hover_range_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("contents");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_1412_(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__3;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Json_mkObj(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_328_(x_10);
x_13 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Json_mkObj(x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonHover___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonHover() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonHover___closed__1;
return x_1;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonMarkupContent____x40_Lean_Data_Lsp_Basic___hyg_1438_(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____spec__1(x_1, x_2);
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
x_6 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_458____closed__2;
x_7 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocationLink____x40_Lean_Data_Lsp_Basic___hyg_565____spec__1(x_1, x_6);
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
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHover___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_fromJsonHover____x40_Lean_Data_Lsp_Hover___hyg_37____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHover() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonHover___closed__1;
return x_1;
}
}
lean_object* l_Lean_Lsp_instFromJsonHoverParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1109_(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
}
lean_object* l_Lean_Lsp_instFromJsonHoverParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonHoverParams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_instToJsonHoverParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1083_(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_Hover(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_Hover_range_x3f___default = _init_l_Lean_Lsp_Hover_range_x3f___default();
lean_mark_persistent(l_Lean_Lsp_Hover_range_x3f___default);
l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1 = _init_l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__1);
l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__2 = _init_l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__2);
l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__3 = _init_l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__3();
lean_mark_persistent(l___private_Lean_Data_Lsp_Hover_0__Lean_Lsp_toJsonHover____x40_Lean_Data_Lsp_Hover___hyg_11____closed__3);
l_Lean_Lsp_instToJsonHover___closed__1 = _init_l_Lean_Lsp_instToJsonHover___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonHover___closed__1);
l_Lean_Lsp_instToJsonHover = _init_l_Lean_Lsp_instToJsonHover();
lean_mark_persistent(l_Lean_Lsp_instToJsonHover);
l_Lean_Lsp_instFromJsonHover___closed__1 = _init_l_Lean_Lsp_instFromJsonHover___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonHover___closed__1);
l_Lean_Lsp_instFromJsonHover = _init_l_Lean_Lsp_instFromJsonHover();
lean_mark_persistent(l_Lean_Lsp_instFromJsonHover);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

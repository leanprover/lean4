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
lean_object* l_Lean_Lsp_instFromJsonHoverParams___boxed(lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonPosition___closed__2;
extern lean_object* l_Lean_Lsp_instFromJsonPosition___closed__1;
extern lean_object* l_Lean_Lsp_instToJsonMarkupContent___closed__2;
extern lean_object* l_Lean_Lsp_instToJsonMarkupContent___closed__1;
lean_object* l_Lean_Lsp_Hover_range_x3f___default;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonLocation___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentPositionParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonHover___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRange___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_Lsp_instToJsonLocationLink___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHoverParams(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonMarkupContent___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonMarkupContent___closed__1;
extern lean_object* l_Lean_Lsp_instFromJsonMarkupContent___closed__2;
lean_object* l_Lean_Lsp_instToJsonHover(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonHover___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHover(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonHover___closed__1;
extern lean_object* l_Lean_Lsp_instFromJsonLocation___closed__1;
extern lean_object* l_Lean_Lsp_instFromJsonLocation___closed__2;
lean_object* l_Lean_Lsp_instFromJsonHover___boxed(lean_object*);
extern lean_object* l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Lsp_Hover_range_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonHover___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Lsp_instFromJsonMarkupContent___closed__1;
x_5 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonMarkupContent___spec__1(x_3, x_4);
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
x_8 = l_Lean_Lsp_instFromJsonMarkupContent___closed__2;
x_9 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_3, x_8);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
}
}
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonHover___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("contents");
return x_1;
}
}
lean_object* l_Lean_Lsp_instFromJsonHover(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_instFromJsonHover___closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonHover___spec__1(x_1, x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Lsp_instFromJsonLocation___closed__2;
x_8 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonLocation___spec__2(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_Lsp_instFromJsonLocation___closed__2;
x_12 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonLocation___spec__2(x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonHover___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonHover___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Lsp_instFromJsonHover___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_instFromJsonHover(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_instToJsonHover(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Lsp_instFromJsonMarkupContent___closed__2;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Lsp_instFromJsonLocation___closed__2;
x_12 = l_Lean_Json_opt___at_Lean_Lsp_instToJsonLocationLink___spec__1(x_11, x_10);
if (x_3 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Lsp_instToJsonMarkupContent___closed__1;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
x_15 = l_Lean_Json_mkObj(x_14);
x_16 = l_Lean_Lsp_instFromJsonHover___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
x_19 = l_Lean_Json_mkObj(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = l_Lean_Lsp_instToJsonMarkupContent___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
x_22 = l_Lean_Json_mkObj(x_21);
x_23 = l_Lean_Lsp_instFromJsonHover___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
x_26 = l_Lean_Json_mkObj(x_25);
return x_26;
}
}
}
lean_object* l_Lean_Lsp_instFromJsonHoverParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonTextDocumentPositionParams___spec__1(x_1, x_2);
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
x_6 = l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonRange___spec__1(x_1, x_6);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lean_Lsp_instFromJsonLocation___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Json_mkObj(x_8);
x_10 = l_Lean_Lsp_instFromJsonTextDocumentEdit___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_JsonNumber_fromNat(x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Lsp_instFromJsonPosition___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Lean_JsonNumber_fromNat(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Lsp_instFromJsonPosition___closed__2;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Json_mkObj(x_23);
x_25 = l_Lean_Lsp_instFromJsonTextDocumentPositionParams___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Json_mkObj(x_28);
return x_29;
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
l_Lean_Lsp_instFromJsonHover___closed__1 = _init_l_Lean_Lsp_instFromJsonHover___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonHover___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

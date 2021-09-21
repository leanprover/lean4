// Lean compiler output
// Module: Lean.Data.Lsp.Workspace
// Imports: Init Lean.Data.Lsp.Basic Lean.Data.Json
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder;
lean_object* l_List_join___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____boxed(lean_object*);
static lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24_(lean_object*);
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder___closed__1;
static lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58_(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_603____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceFolder;
static lean_object* _init_l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uri");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("name");
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_inc(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_10 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_join___rarg(x_14);
x_16 = l_Lean_Json_mkObj(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWorkspaceFolder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonWorkspaceFolder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instToJsonWorkspaceFolder___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonLocation____x40_Lean_Data_Lsp_Basic___hyg_603____spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2;
x_9 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_fromJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_58____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceFolder() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__1;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Workspace(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1 = _init_l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1();
lean_mark_persistent(l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__1);
l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2 = _init_l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2();
lean_mark_persistent(l___private_Lean_Data_Lsp_Workspace_0__Lean_Lsp_toJsonWorkspaceFolder____x40_Lean_Data_Lsp_Workspace___hyg_24____closed__2);
l_Lean_Lsp_instToJsonWorkspaceFolder___closed__1 = _init_l_Lean_Lsp_instToJsonWorkspaceFolder___closed__1();
lean_mark_persistent(l_Lean_Lsp_instToJsonWorkspaceFolder___closed__1);
l_Lean_Lsp_instToJsonWorkspaceFolder = _init_l_Lean_Lsp_instToJsonWorkspaceFolder();
lean_mark_persistent(l_Lean_Lsp_instToJsonWorkspaceFolder);
l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__1 = _init_l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__1();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWorkspaceFolder___closed__1);
l_Lean_Lsp_instFromJsonWorkspaceFolder = _init_l_Lean_Lsp_instFromJsonWorkspaceFolder();
lean_mark_persistent(l_Lean_Lsp_instFromJsonWorkspaceFolder);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

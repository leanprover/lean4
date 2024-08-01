// Lean compiler output
// Module: Init.Data.List.Attach
// Imports: Init.Data.List.Count Init.Data.Subtype
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
LEAN_EXPORT lean_object* l_List_attach___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__Option_pmap_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__Option_pmap_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl(lean_object*);
LEAN_EXPORT lean_object* l_List_pmap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmapImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_attach___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmapImpl___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_attach(lean_object*);
LEAN_EXPORT lean_object* l_List_pmap___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_pmap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_6, lean_box(0));
x_9 = l_List_pmap___rarg(x_1, x_7, lean_box(0));
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_10, lean_box(0));
x_13 = l_List_pmap___rarg(x_1, x_11, lean_box(0));
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_pmap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_pmap___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Data_List_Attach_0__List_pmap_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_List_Attach_0__List_attachWithImpl___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_attachWithImpl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_Attach_0__List_attachWithImpl___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_attach___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_attach(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_attach___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_attach___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_attach___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1___rarg(x_1, x_6);
x_8 = lean_apply_2(x_1, x_5, lean_box(0));
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1___rarg(x_1, x_10);
x_12 = lean_apply_2(x_1, x_9, lean_box(0));
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmapImpl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at___private_Init_Data_List_Attach_0__List_pmapImpl___spec__1___rarg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__List_pmapImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Data_List_Attach_0__List_pmapImpl___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__Option_pmap_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Attach_0__Option_pmap_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Init_Data_List_Attach_0__Option_pmap_match__1_splitter___rarg), 4, 0);
return x_4;
}
}
lean_object* initialize_Init_Data_List_Count(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Subtype(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Attach(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Count(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

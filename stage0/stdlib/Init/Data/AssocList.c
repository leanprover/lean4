// Lean compiler output
// Module: Init.Data.AssocList
// Imports: Init.Control.Id
#include "runtime/lean.h"
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
lean_object* l_AssocList_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_AssocList_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_AssocList_foldl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main(lean_object*, lean_object*);
uint8_t l_AssocList_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main(lean_object*, lean_object*);
lean_object* l_AssocList_erase___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_empty(lean_object*, lean_object*);
lean_object* l_AssocList_find___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace(lean_object*, lean_object*);
lean_object* l_AssocList_contains(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main(lean_object*, lean_object*);
lean_object* l_AssocList_foldl(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_erase(lean_object*, lean_object*);
lean_object* l_AssocList_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_erase___main(lean_object*, lean_object*);
lean_object* l_AssocList_erase___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_AssocList_foldlM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_foldlM___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_AssocList_foldlM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_apply_3(x_2, x_3, x_8, x_9);
x_13 = lean_alloc_closure((void*)(l_AssocList_foldlM___main___rarg___lambda__1), 4, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_10);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
lean_object* l_AssocList_foldlM___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_AssocList_foldlM___main___rarg), 4, 0);
return x_5;
}
}
lean_object* l_AssocList_foldlM___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_foldlM___main(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_AssocList_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_foldlM___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_AssocList_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_AssocList_foldlM___rarg), 4, 0);
return x_5;
}
}
lean_object* l_AssocList_foldlM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_foldlM(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_AssocList_foldlM___main___at_AssocList_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
lean_object* l_AssocList_foldlM___main___at_AssocList_foldl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_AssocList_foldlM___main___at_AssocList_foldl___spec__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_AssocList_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_AssocList_foldlM___main___at_AssocList_foldl___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_AssocList_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_AssocList_foldl___rarg), 3, 0);
return x_4;
}
}
lean_object* l_AssocList_find___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_5, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
}
}
lean_object* l_AssocList_find___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_find___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_AssocList_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_AssocList_find___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_AssocList_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_find___rarg), 3, 0);
return x_3;
}
}
uint8_t l_AssocList_contains___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_5, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
}
}
}
lean_object* l_AssocList_contains___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_contains___main___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_AssocList_contains___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_AssocList_contains___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_AssocList_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_AssocList_contains___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_AssocList_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_contains___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_AssocList_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_AssocList_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_AssocList_replace___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_9 = lean_apply_2(x_1, x_6, x_2);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_AssocList_replace___main___rarg(x_1, x_2, x_3, x_8);
lean_ctor_set(x_4, 2, x_11);
return x_4;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_12);
x_15 = lean_apply_2(x_1, x_12, x_2);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_AssocList_replace___main___rarg(x_1, x_2, x_3, x_14);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_14);
return x_19;
}
}
}
}
}
lean_object* l_AssocList_replace___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_replace___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_AssocList_replace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_replace___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_AssocList_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_replace___rarg), 4, 0);
return x_3;
}
}
lean_object* l_AssocList_erase___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_5);
x_8 = lean_apply_2(x_1, x_5, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_AssocList_erase___main___rarg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_11);
x_14 = lean_apply_2(x_1, x_11, x_2);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_AssocList_erase___main___rarg(x_1, x_2, x_13);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
}
lean_object* l_AssocList_erase___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_erase___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_AssocList_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_AssocList_erase___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_AssocList_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_AssocList_erase___rarg), 3, 0);
return x_3;
}
}
lean_object* initialize_Init_Control_Id(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_AssocList(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

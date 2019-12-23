// Lean compiler output
// Module: Init.Data.List.Control
// Imports: Init.Control.Monad Init.Control.Alternative Init.Data.List.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_List_filterAuxM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_foldlM(lean_object*);
lean_object* l_List_forA___boxed(lean_object*);
lean_object* l_List_foldlM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forA_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterM___boxed(lean_object*);
lean_object* l_List_mapM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM_u2082(lean_object*);
lean_object* l_List_allM___boxed(lean_object*);
lean_object* l_List_mapA___main(lean_object*);
lean_object* l_List_filterAuxM___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM_u2082___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_anyM___main___boxed(lean_object*);
lean_object* l_List_forA___main___boxed(lean_object*);
lean_object* l_List_forA___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapA___main___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_List_firstM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_anyM___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_allM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_firstM___main(lean_object*);
lean_object* l_List_filterM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_allM(lean_object*);
lean_object* l_List_forA_u2082___boxed(lean_object*);
lean_object* l_List_mapM(lean_object*);
lean_object* l_List_filterAuxM___main___boxed(lean_object*);
lean_object* l_List_mapM_u2082___main___boxed(lean_object*);
lean_object* l_List_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_anyM(lean_object*);
lean_object* l_List_allM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_firstM___main___boxed(lean_object*);
lean_object* l_List_mapA_u2082___boxed(lean_object*);
lean_object* l_List_firstM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM_u2082___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM_u2082(lean_object*);
lean_object* l_List_forA_u2082___main___boxed(lean_object*);
lean_object* l_List_foldlM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterRevM___boxed(lean_object*);
lean_object* l_List_mapM_u2082___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM_u2082___main(lean_object*);
lean_object* l_List_allM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_mapA_u2082___main(lean_object*);
lean_object* l_List_forM_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___boxed(lean_object*);
lean_object* l_List_filterAuxM___boxed(lean_object*);
lean_object* l_List_allM___main___boxed(lean_object*);
lean_object* l_List_foldrM___main___boxed(lean_object*);
lean_object* l_List_filterAuxM___main(lean_object*);
lean_object* l_List_mapM___boxed(lean_object*);
lean_object* l_List_mapA_u2082___main___boxed(lean_object*);
lean_object* l_List_forA_u2082___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forA___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_allM___main(lean_object*);
lean_object* l_List_forM_u2082___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapA___boxed(lean_object*);
lean_object* l_List_foldlM___main(lean_object*);
lean_object* l_List_forM_u2082___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM_u2082___boxed(lean_object*);
lean_object* l_List_allM___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main(lean_object*);
lean_object* l_List_mapA___main___rarg___closed__1;
lean_object* l_List_forM_u2082___main(lean_object*);
lean_object* l_List_mapA(lean_object*);
lean_object* l_List_mapM_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___boxed(lean_object*);
lean_object* l_List_mapA_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapA___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main(lean_object*);
lean_object* l_List_forA___main(lean_object*);
lean_object* l_List_forM___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrM___main(lean_object*);
lean_object* l_List_filterM___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___boxed(lean_object*);
lean_object* l_List_anyM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM_u2082___main___boxed(lean_object*);
lean_object* l_List_forA_u2082(lean_object*);
lean_object* l_List_firstM(lean_object*, lean_object*);
lean_object* l_List_forM___boxed(lean_object*);
lean_object* l_List_mapA___main___boxed(lean_object*);
lean_object* l_List_mapA_u2082(lean_object*);
lean_object* l_List_foldrM___boxed(lean_object*);
lean_object* l_List_forA(lean_object*);
lean_object* l_List_mapA_u2082___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM(lean_object*);
lean_object* l_List_mapA___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_anyM___boxed(lean_object*);
lean_object* l_List_forM_u2082___boxed(lean_object*);
lean_object* l_List_firstM___boxed(lean_object*, lean_object*);
lean_object* l_List_mapM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forA_u2082___main(lean_object*);
lean_object* l_List_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterRevM(lean_object*);
lean_object* l_List_filterM(lean_object*);
lean_object* l_List_anyM___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM(lean_object*);
lean_object* l_List_foldrM(lean_object*);
lean_object* l_List_mapM___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___boxed(lean_object*);
lean_object* l_List_anyM___main(lean_object*);
lean_object* l_List_anyM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_List_mapM___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = l_List_mapM___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_List_mapM___main___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_List_mapM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_4);
x_13 = lean_apply_1(x_4, x_10);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_List_mapM___main___rarg___lambda__2), 5, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_mapM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapM___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mapM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_mapM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mapM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM_u2082___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = l_List_mapM_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_4);
x_8 = lean_alloc_closure((void*)(l_List_mapM___main___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_List_mapM_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
x_14 = lean_box(0);
x_8 = x_14;
goto block_13;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_box(0);
x_8 = x_15;
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_5);
x_21 = lean_apply_2(x_5, x_16, x_18);
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_List_mapM_u2082___main___rarg___lambda__1), 6, 5);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_17);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_20);
x_23 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
}
lean_object* l_List_mapM_u2082___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapM_u2082___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mapM_u2082___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapM_u2082___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_mapM_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapM_u2082___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mapM_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapM_u2082(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapA___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_List_mapA___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_mapA___main___rarg___lambda__1), 2, 0);
return x_1;
}
}
lean_object* l_List_mapA___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
x_14 = lean_apply_1(x_4, x_9);
x_15 = l_List_mapA___main___rarg___closed__1;
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_14);
x_17 = l_List_mapA___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_10);
x_18 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
}
lean_object* l_List_mapA___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapA___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mapA___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapA___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapA___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapA___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_mapA(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapA___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mapA___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapA(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapA_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
x_13 = lean_box(0);
x_8 = x_13;
goto block_12;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_box(0);
x_8 = x_14;
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_5);
x_22 = lean_apply_2(x_5, x_15, x_17);
x_23 = l_List_mapA___main___rarg___closed__1;
x_24 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_23, x_22);
x_25 = l_List_mapA_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_16, x_18);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l_List_mapA_u2082___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapA_u2082___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mapA_u2082___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapA_u2082___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapA_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapA_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_mapA_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapA_u2082___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mapA_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mapA_u2082(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
lean_object* l_List_forM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_4);
x_13 = lean_apply_1(x_4, x_10);
x_14 = lean_alloc_closure((void*)(l_List_forM___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_forM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_forM___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_List_forM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_forM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM_u2082___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_List_forM_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
x_14 = lean_box(0);
x_8 = x_14;
goto block_13;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_box(0);
x_8 = x_15;
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_5);
x_21 = lean_apply_2(x_5, x_16, x_18);
x_22 = lean_alloc_closure((void*)(l_List_forM_u2082___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_17);
lean_closure_set(x_22, 3, x_19);
x_23 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
}
lean_object* l_List_forM_u2082___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM_u2082___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_forM_u2082___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forM_u2082___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_List_forM_u2082___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forM_u2082___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_forM_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forM_u2082___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_forM_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forM_u2082(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forA___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_4);
x_12 = lean_apply_1(x_4, x_9);
x_13 = l_List_forA___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_10);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
lean_object* l_List_forA___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forA___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_forA___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forA___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forA___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forA___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_forA(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forA___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_forA___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forA(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forA_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_inc(x_5);
x_19 = lean_apply_2(x_5, x_14, x_16);
x_20 = l_List_forA_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_15, x_17);
x_21 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_List_forA_u2082___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forA_u2082___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_forA_u2082___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forA_u2082___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forA_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forA_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_forA_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forA_u2082___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_forA_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_forA_u2082(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = l_List_filterAuxM___main___rarg(x_1, lean_box(0), x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_4);
x_9 = l_List_filterAuxM___main___rarg(x_1, lean_box(0), x_2, x_3, x_8);
return x_9;
}
}
}
lean_object* l_List_filterAuxM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_9);
x_12 = lean_apply_1(x_3, x_9);
x_13 = lean_alloc_closure((void*)(l_List_filterAuxM___main___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_9);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
lean_object* l_List_filterAuxM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterAuxM___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_filterAuxM___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_List_filterAuxM___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* l_List_filterAuxM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_filterAuxM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_filterAuxM___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_filterAuxM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterAuxM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_filterAuxM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_filterAuxM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_filterM___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_List_reverse___rarg(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_List_filterM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = l_List_filterAuxM___main___rarg(x_1, lean_box(0), x_3, x_4, x_6);
x_8 = lean_alloc_closure((void*)(l_List_filterM___rarg___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_List_filterM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_filterM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_filterM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_filterRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_List_reverse___rarg(x_4);
x_6 = lean_box(0);
x_7 = l_List_filterAuxM___main___rarg(x_1, lean_box(0), x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_List_filterRevM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_filterRevM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_filterRevM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_filterRevM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_List_foldlM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_4);
x_13 = lean_apply_2(x_4, x_5, x_10);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___main___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_foldlM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_foldlM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_foldlM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_List_foldlM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_foldlM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_foldlM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_foldrM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_4);
x_13 = l_List_foldrM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_11);
x_14 = lean_apply_1(x_4, x_10);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_foldrM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldrM___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_foldrM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_foldrM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_foldrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldrM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_List_foldrM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldrM___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_foldrM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_foldrM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_firstM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_4);
x_11 = lean_apply_1(x_4, x_8);
x_12 = l_List_firstM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_9);
x_13 = lean_apply_3(x_10, lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_List_firstM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_firstM___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_firstM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_firstM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_firstM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_firstM___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_firstM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_firstM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_List_firstM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_firstM(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_anyM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_List_anyM___main___rarg(x_1, lean_box(0), x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
}
lean_object* l_List_anyM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_apply_1(x_3, x_10);
x_14 = lean_alloc_closure((void*)(l_List_anyM___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_anyM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_anyM___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_anyM___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_List_anyM___main___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_List_anyM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_anyM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_anyM___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_List_anyM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_anyM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_anyM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_anyM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_allM___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_List_allM___main___rarg(x_1, lean_box(0), x_2, x_3);
return x_9;
}
}
}
lean_object* l_List_allM___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_apply_1(x_3, x_10);
x_14 = lean_alloc_closure((void*)(l_List_allM___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_allM___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_allM___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_allM___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_List_allM___main___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_List_allM___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_allM___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_allM___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_List_allM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_allM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_allM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_allM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Control_Monad(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Data_List_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_List_Control(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Monad(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_mapA___main___rarg___closed__1 = _init_l_List_mapA___main___rarg___closed__1();
lean_mark_persistent(l_List_mapA___main___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

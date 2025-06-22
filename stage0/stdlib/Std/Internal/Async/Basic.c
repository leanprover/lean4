// Lean compiler output
// Module: Std.Internal.Async.Basic
// Imports: Init.Core Init.System.IO Init.System.Promise
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
static lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_pure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise___redArg___boxed(lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise(lean_object*, lean_object*);
lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_block___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_map___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bindIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bindIO___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bind___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_mapIO___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bindIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_pure(lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_mapIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Std_Internal_IO_Async_AsyncTask_instPure___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_mapIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_instPure;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_block(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_pure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_task_pure(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_pure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_task_pure(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_AsyncTask_instPure___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_pure), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_AsyncTask_instPure() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_AsyncTask_instPure___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bind___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_task_pure(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_task_pure(x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bind___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = lean_task_bind(x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_bind___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = lean_task_bind(x_3, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_map___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = lean_task_map(x_3, x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_map___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
x_9 = lean_task_map(x_5, x_4, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bindIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_4 = x_10;
x_5 = x_3;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_2(x_1, x_11, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_4 = x_17;
x_5 = x_18;
goto block_9;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_task_pure(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bindIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_bindIO___redArg___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_io_bind_task(x_1, x_4, x_5, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_bindIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_bindIO___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = lean_io_bind_task(x_3, x_6, x_7, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_mapIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_4 = x_9;
x_5 = x_3;
goto block_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_2(x_1, x_11, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_2);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_4 = x_18;
x_5 = x_19;
goto block_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_apply_2(x_1, x_20, x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_4 = x_27;
x_5 = x_28;
goto block_8;
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_mapIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_mapIO___redArg___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_io_map_task(x_4, x_2, x_5, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_mapIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_AsyncTask_mapIO___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = lean_io_map_task(x_6, x_4, x_7, x_9, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_block___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_task_get_own(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_block(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_AsyncTask_block___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Promise_result_x21___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Promise_result_x21___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_AsyncTask_ofPromise___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPromise___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_AsyncTask_ofPromise(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Except_pure), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0;
x_3 = l_IO_Promise_result_x21___redArg(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = lean_task_map(x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0;
x_4 = l_IO_Promise_result_x21___redArg(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = lean_task_map(x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_AsyncTask_ofPurePromise(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_get_task_state(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_get_task_state(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_AsyncTask_getState___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_AsyncTask_getState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_AsyncTask_getState(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_AsyncTask_instPure___closed__0 = _init_l_Std_Internal_IO_Async_AsyncTask_instPure___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_AsyncTask_instPure___closed__0);
l_Std_Internal_IO_Async_AsyncTask_instPure = _init_l_Std_Internal_IO_Async_AsyncTask_instPure();
lean_mark_persistent(l_Std_Internal_IO_Async_AsyncTask_instPure);
l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0 = _init_l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_AsyncTask_ofPurePromise___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

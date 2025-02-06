// Lean compiler output
// Module: Lean.Server.AsyncList
// Imports: Init.System.IO Init.System.Promise
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
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__2;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg(lean_object*, uint32_t, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitHead_x3f___rarg___closed__1;
static lean_object* l_IO_AsyncList_getFinishedPrefix___rarg___closed__2;
static lean_object* l_IO_AsyncList_getFinishedPrefix___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__2(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AsyncList_waitHead_x3f___rarg___lambda__1(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_IO_AsyncList_instAppend(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cancel___rarg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___rarg(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_IO_AsyncList_getAll___rarg___closed__1;
static lean_object* l_IO_AsyncList_waitAll___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg___lambda__2(lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*, lean_object*);
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll___rarg(lean_object*);
static lean_object* l_IO_AsyncList_instCoeList___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg(lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
static lean_object* l_IO_AsyncList_instAppend___closed__1;
static lean_object* l_IO_AsyncList_getFinishedPrefix___rarg___closed__4;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___lambda__2(lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_IO_sleep___boxed(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Task_Priority_dedicated;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___rarg___closed__2;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___rarg(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitUntil___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__2;
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object*, uint32_t, lean_object*);
static lean_object* l_IO_AsyncList_getFinishedPrefix___rarg___closed__3;
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_append___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_IO_AsyncList_append___rarg(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_IO_AsyncList_append___rarg(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Task_Priority_default;
x_15 = 0;
x_16 = lean_task_map(x_13, x_11, x_14, x_15);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg___lambda__1), 2, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Task_Priority_default;
x_21 = 0;
x_22 = lean_task_map(x_19, x_17, x_20, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_instAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instAppend(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_instAppend___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(x_1, x_4);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(2);
x_3 = l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_ofList___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_instCoeList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_ofList___rarg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_instCoeList___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(2);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 3, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_15);
x_20 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Task_Priority_default;
x_22 = lean_io_as_task(x_20, x_21, x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set(x_22, 0, x_5);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_6, 0, x_25);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 3, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_15);
x_30 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Task_Priority_default;
x_32 = lean_io_as_task(x_30, x_31, x_13);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_28);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_40 = x_6;
} else {
 lean_dec_ref(x_6);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 3, 2);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_38);
x_42 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = l_Task_Priority_default;
x_44 = lean_io_as_task(x_42, x_43, x_13);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_40;
}
lean_ctor_set(x_48, 0, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_4);
if (x_51 == 0)
{
return x_4;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_4);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Task_Priority_default;
x_7 = lean_io_as_task(x_5, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync___rarg), 3, 0);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_getAll___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll___rarg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_IO_AsyncList_getAll___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_IO_AsyncList_getAll___rarg(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_task_get_own(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_1 = x_27;
goto _start;
}
}
default: 
{
lean_object* x_29; 
x_29 = l_IO_AsyncList_getAll___rarg___closed__1;
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_getAll___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_task_pure(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_task_pure(x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_IO_AsyncList_waitUntil___rarg(x_1, x_12);
return x_13;
}
}
}
static lean_object* _init_l_IO_AsyncList_waitUntil___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_getAll___rarg___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_inc(x_4);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_free_object(x_2);
x_8 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___rarg___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_4);
x_9 = l_IO_AsyncList_waitUntil___rarg(x_1, x_5);
x_10 = l_Task_Priority_default;
x_11 = 0;
x_12 = lean_task_map(x_8, x_9, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_task_pure(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_17);
x_19 = lean_apply_1(x_1, x_17);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___rarg___lambda__1), 2, 1);
lean_closure_set(x_21, 0, x_17);
x_22 = l_IO_AsyncList_waitUntil___rarg(x_1, x_18);
x_23 = l_Task_Priority_default;
x_24 = 0;
x_25 = lean_task_map(x_21, x_22, x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_task_pure(x_29);
return x_30;
}
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
x_32 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___rarg___lambda__2), 2, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Task_Priority_default;
x_34 = 0;
x_35 = lean_task_bind(x_31, x_32, x_33, x_34);
return x_35;
}
default: 
{
lean_object* x_36; 
lean_dec(x_1);
x_36 = l_IO_AsyncList_waitUntil___rarg___closed__1;
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitAll___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_AsyncList_waitAll___rarg___closed__1;
x_3 = l_IO_AsyncList_waitUntil___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_IO_AsyncList_waitAll___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_IO_AsyncList_waitFind_x3f___rarg(x_1, x_8);
return x_9;
}
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitFind_x3f___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_waitFind_x3f___rarg___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_task_pure(x_9);
return x_10;
}
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___rarg___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Task_Priority_default;
x_14 = 0;
x_15 = lean_task_bind(x_11, x_12, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_IO_AsyncList_waitFind_x3f___rarg___closed__2;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___rarg), 2, 0);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_IO_AsyncList_getFinishedPrefix___rarg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_7, 0, x_1);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_7, 1, x_17);
lean_ctor_set(x_7, 0, x_1);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_21 = x_8;
} else {
 lean_dec_ref(x_8);
 x_21 = lean_box(0);
}
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_18);
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_29 = x_8;
} else {
 lean_dec_ref(x_8);
 x_29 = lean_box(0);
}
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_25);
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_26)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_26;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_1);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
return x_6;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l_IO_AsyncList_getFinishedPrefix___rarg(x_38, x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_44);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_43)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_43;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
case 1:
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_81; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_81 = lean_io_get_task_state(x_57, x_2);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 2)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 1;
x_58 = x_84;
x_59 = x_83;
goto block_80;
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_82);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = 0;
x_58 = x_86;
x_59 = x_85;
goto block_80;
}
}
else
{
uint8_t x_87; 
lean_dec(x_57);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
return x_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
block_80:
{
if (x_58 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
x_60 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__2;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_task_get_own(x_57);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_box(0);
lean_ctor_set_tag(x_62, 1);
x_65 = 1;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_59);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_70);
x_73 = 1;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_59);
return x_77;
}
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_62, 0);
lean_inc(x_78);
lean_dec(x_62);
x_1 = x_78;
x_2 = x_59;
goto _start;
}
}
}
}
default: 
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__4;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_2);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefix___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(x_1, x_2, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_9, 0, x_3);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_3);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_20);
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_28 = x_9;
} else {
 lean_dec_ref(x_9);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_31 = x_10;
} else {
 lean_dec_ref(x_10);
 x_31 = lean_box(0);
}
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_27);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_28)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_28;
}
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_3);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_41 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(x_1, x_2, x_40, x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_45 = x_41;
} else {
 lean_dec_ref(x_41);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_46);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_49);
if (lean_is_scalar(x_47)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_47;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_45)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_45;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_39);
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_57 = x_41;
} else {
 lean_dec_ref(x_41);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
case 1:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_3, 0);
lean_inc(x_59);
lean_dec(x_3);
x_60 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__1;
x_61 = l_Task_Priority_default;
x_62 = 1;
x_63 = lean_task_map(x_60, x_59, x_61, x_62);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_box(0);
lean_inc(x_2);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_io_wait_any(x_66, x_4);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_68);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__2;
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
x_73 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__2;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
lean_dec(x_68);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_67);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_67, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_ctor_set_tag(x_75, 1);
x_79 = lean_box(x_62);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_64);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_67, 0, x_81);
return x_67;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_75, 0);
lean_inc(x_82);
lean_dec(x_75);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_box(x_62);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_67, 0, x_86);
return x_67;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_87 = lean_ctor_get(x_67, 1);
lean_inc(x_87);
lean_dec(x_67);
x_88 = lean_ctor_get(x_75, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_89 = x_75;
} else {
 lean_dec_ref(x_75);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
 lean_ctor_set_tag(x_90, 1);
}
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_box(x_62);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_64);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_67, 1);
lean_inc(x_95);
lean_dec(x_67);
x_96 = lean_ctor_get(x_75, 0);
lean_inc(x_96);
lean_dec(x_75);
x_3 = x_96;
x_4 = x_95;
goto _start;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_67);
if (x_98 == 0)
{
return x_67;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_67, 0);
x_100 = lean_ctor_get(x_67, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_67);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
x_103 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__2;
x_104 = lean_task_map(x_103, x_102, x_61, x_62);
x_105 = lean_box(0);
lean_inc(x_2);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_2);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_63);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_io_wait_any(x_108, x_4);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
x_113 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__2;
lean_ctor_set(x_109, 0, x_113);
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_dec(x_109);
x_115 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__2;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_110, 0);
lean_inc(x_117);
lean_dec(x_110);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_1);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_1, 0);
lean_dec(x_119);
x_120 = !lean_is_exclusive(x_109);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_109, 0);
lean_dec(x_121);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
lean_ctor_set(x_1, 0, x_122);
x_123 = lean_box(x_62);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_105);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_109, 0, x_125);
return x_109;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_dec(x_109);
x_127 = lean_ctor_get(x_117, 0);
lean_inc(x_127);
lean_dec(x_117);
lean_ctor_set(x_1, 0, x_127);
x_128 = lean_box(x_62);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_105);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_1);
x_132 = lean_ctor_get(x_109, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_133 = x_109;
} else {
 lean_dec_ref(x_109);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_117, 0);
lean_inc(x_134);
lean_dec(x_117);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_box(x_62);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_105);
lean_ctor_set(x_138, 1, x_137);
if (lean_is_scalar(x_133)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_133;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_132);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_109, 1);
lean_inc(x_140);
lean_dec(x_109);
x_141 = lean_ctor_get(x_117, 0);
lean_inc(x_141);
lean_dec(x_117);
x_3 = x_141;
x_4 = x_140;
goto _start;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_109);
if (x_143 == 0)
{
return x_109;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_109, 0);
x_145 = lean_ctor_get(x_109, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_109);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
default: 
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_2);
lean_dec(x_1);
x_147 = l_IO_AsyncList_getFinishedPrefix___rarg___closed__4;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_4);
return x_148;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint8_t x_6; 
x_5 = 0;
x_6 = lean_uint32_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box_uint32(x_2);
x_8 = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__1;
x_10 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Task_Priority_dedicated;
x_12 = lean_io_as_task(x_10, x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(x_3, x_13, x_1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__2;
x_21 = l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg(x_3, x_20, x_1, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__1(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box_uint32(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_sleep___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Task_Priority_dedicated;
x_8 = lean_io_as_task(x_6, x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_io_wait_any(x_13, x_10);
lean_dec(x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__2(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = l_IO_sleep(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_24; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_24 = lean_io_get_task_state(x_16, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 2)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_17 = x_27;
x_18 = x_26;
goto block_23;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_25);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = 0;
x_17 = x_29;
x_18 = x_28;
goto block_23;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
block_23:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__1(x_2, x_16, x_19, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 0;
x_5 = lean_uint32_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__2(x_1, x_2, x_6, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_6 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___lambda__2(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_mono_ms_now(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg(x_1, x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_io_mono_ms_now(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_sub(x_12, x_6);
lean_dec(x_6);
lean_dec(x_12);
x_15 = lean_uint32_to_nat(x_2);
x_16 = lean_nat_sub(x_15, x_14);
lean_dec(x_14);
lean_dec(x_15);
x_17 = lean_uint32_of_nat(x_16);
lean_dec(x_16);
x_18 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(x_3, x_17, x_13);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_9);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
return x_5;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_6 = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_IO_AsyncList_waitHead_x3f___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitHead_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_waitHead_x3f___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_AsyncList_waitHead_x3f___rarg___closed__1;
x_3 = l_IO_AsyncList_waitFind_x3f___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_waitHead_x3f___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_IO_AsyncList_waitHead_x3f___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_cancel___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_1 = x_3;
goto _start;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_io_cancel(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_io_get_task_state(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_task_get_own(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; 
lean_free_object(x_8);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_task_get_own(x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_1 = x_21;
x_2 = x_17;
goto _start;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
return x_6;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
default: 
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_cancel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_cancel___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_AsyncList_instAppend___closed__1 = _init_l_IO_AsyncList_instAppend___closed__1();
lean_mark_persistent(l_IO_AsyncList_instAppend___closed__1);
l_IO_AsyncList_instCoeList___closed__1 = _init_l_IO_AsyncList_instCoeList___closed__1();
lean_mark_persistent(l_IO_AsyncList_instCoeList___closed__1);
l_IO_AsyncList_getAll___rarg___closed__1 = _init_l_IO_AsyncList_getAll___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_getAll___rarg___closed__1);
l_IO_AsyncList_waitUntil___rarg___closed__1 = _init_l_IO_AsyncList_waitUntil___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitUntil___rarg___closed__1);
l_IO_AsyncList_waitAll___rarg___closed__1 = _init_l_IO_AsyncList_waitAll___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitAll___rarg___closed__1);
l_IO_AsyncList_waitFind_x3f___rarg___closed__1 = _init_l_IO_AsyncList_waitFind_x3f___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___rarg___closed__1);
l_IO_AsyncList_waitFind_x3f___rarg___closed__2 = _init_l_IO_AsyncList_waitFind_x3f___rarg___closed__2();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___rarg___closed__2);
l_IO_AsyncList_getFinishedPrefix___rarg___closed__1 = _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefix___rarg___closed__1);
l_IO_AsyncList_getFinishedPrefix___rarg___closed__2 = _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__2();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefix___rarg___closed__2);
l_IO_AsyncList_getFinishedPrefix___rarg___closed__3 = _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__3();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefix___rarg___closed__3);
l_IO_AsyncList_getFinishedPrefix___rarg___closed__4 = _init_l_IO_AsyncList_getFinishedPrefix___rarg___closed__4();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefix___rarg___closed__4);
l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__1 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__1);
l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__2 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__2();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout_go___rarg___closed__2);
l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___lambda__2___closed__1);
l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__1 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__1);
l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__2 = _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__2();
lean_mark_persistent(l_IO_AsyncList_getFinishedPrefixWithTimeout___rarg___closed__2);
l_IO_AsyncList_waitHead_x3f___rarg___closed__1 = _init_l_IO_AsyncList_waitHead_x3f___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitHead_x3f___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

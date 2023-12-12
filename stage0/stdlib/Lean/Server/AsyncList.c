// Lean compiler output
// Module: Lean.Server.AsyncList
// Imports: Init Init.System.IO
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
lean_object* lean_io_cancel(lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabitedAsyncList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg(lean_object*);
static lean_object* l_IO_AsyncList_waitHead_x3f___rarg___closed__1;
lean_object* lean_io_has_finished(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AsyncList_waitHead_x3f___rarg___lambda__1(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cancel___rarg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_getAll___rarg___closed__1;
static lean_object* l_IO_AsyncList_waitAll___rarg___closed__1;
static lean_object* l_IO_AsyncList_instAppendAsyncList___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg___lambda__2(lean_object*, lean_object*);
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeListAsyncList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_AsyncList_waitAll___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instAppendAsyncList(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_instCoeListAsyncList___closed__1;
static lean_object* l_IO_AsyncList_waitFind_x3f___rarg___closed__2;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitHead_x3f___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___rarg(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitUntil___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_waitUntil(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabitedAsyncList(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Task_Priority_default;
x_15 = lean_task_map(x_13, x_11, x_14);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg___lambda__1), 2, 1);
lean_closure_set(x_17, 0, x_2);
x_18 = lean_alloc_closure((void*)(l_Except_map___rarg), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = l_Task_Priority_default;
x_20 = lean_task_map(x_18, x_16, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
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
static lean_object* _init_l_IO_AsyncList_instAppendAsyncList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_append___rarg), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instAppendAsyncList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_instAppendAsyncList___closed__1;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
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
lean_dec(x_1);
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
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_instCoeListAsyncList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_ofList___rarg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeListAsyncList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_AsyncList_instCoeListAsyncList___closed__1;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
x_17 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Task_Priority_default;
x_19 = lean_io_as_task(x_17, x_18, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_IO_AsyncList_getAll___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_task_get_own(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_1 = x_18;
goto _start;
}
}
default: 
{
lean_object* x_20; 
x_20 = l_IO_AsyncList_getAll___rarg___closed__1;
return x_20;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_task_pure(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_IO_AsyncList_waitUntil___rarg(x_1, x_8);
return x_9;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_3);
x_8 = l_IO_AsyncList_waitUntil___rarg(x_1, x_4);
x_9 = l_Task_Priority_default;
x_10 = lean_task_map(x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_task_pure(x_14);
return x_15;
}
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_alloc_closure((void*)(l_IO_AsyncList_waitUntil___rarg___lambda__2), 2, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = l_Task_Priority_default;
x_19 = lean_task_bind(x_16, x_17, x_18);
return x_19;
}
default: 
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = l_IO_AsyncList_waitUntil___rarg___closed__1;
return x_20;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___rarg___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Task_Priority_default;
x_14 = lean_task_bind(x_11, x_12, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_IO_AsyncList_waitFind_x3f___rarg___closed__2;
return x_15;
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
LEAN_EXPORT lean_object* l_IO_AsyncList_getFinishedPrefix___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_IO_AsyncList_getFinishedPrefix___rarg(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_7, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_17);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
return x_5;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_5, 0);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_5);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_io_has_finished(x_27, x_2);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_27);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = l_IO_AsyncList_getAll___rarg___closed__1;
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l_IO_AsyncList_getAll___rarg___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 1);
x_39 = lean_ctor_get(x_28, 0);
lean_dec(x_39);
x_40 = lean_task_get_own(x_27);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_28, 0, x_44);
return x_28;
}
else
{
lean_object* x_45; 
lean_free_object(x_28);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_1 = x_45;
x_2 = x_38;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_task_get_own(x_27);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_1 = x_54;
x_2 = x_47;
goto _start;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
return x_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_28, 0);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_28);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
default: 
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_IO_AsyncList_getAll___rarg___closed__1;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_2);
return x_61;
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
x_8 = lean_io_has_finished(x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = lean_task_get_own(x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_22; 
lean_free_object(x_8);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_1 = x_22;
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_task_get_own(x_5);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_25);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_1 = x_28;
x_2 = x_24;
goto _start;
}
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
default: 
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_2);
return x_39;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_AsyncList_instAppendAsyncList___closed__1 = _init_l_IO_AsyncList_instAppendAsyncList___closed__1();
lean_mark_persistent(l_IO_AsyncList_instAppendAsyncList___closed__1);
l_IO_AsyncList_instCoeListAsyncList___closed__1 = _init_l_IO_AsyncList_instCoeListAsyncList___closed__1();
lean_mark_persistent(l_IO_AsyncList_instCoeListAsyncList___closed__1);
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
l_IO_AsyncList_waitHead_x3f___rarg___closed__1 = _init_l_IO_AsyncList_waitHead_x3f___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitHead_x3f___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

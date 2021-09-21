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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll___rarg(lean_object*);
static lean_object* l_IO_AsyncList_getAll___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_finishedPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instInhabitedAsyncList(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___rarg___closed__2;
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_instAppendAsyncList___closed__1;
static lean_object* l_IO_AsyncList_instCoeListAsyncList___closed__1;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at_IO_AsyncList_ofList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instCoeListAsyncList(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitAll___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_finishedPrefix___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_updateFinishedPrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_waitFind_x3f___rarg___closed__1;
extern lean_object* l_Task_Priority_default;
lean_object* lean_io_has_finished(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_updateFinishedPrefix___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_finishedPrefix___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_getAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_instAppendAsyncList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_ofList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_IO_AsyncList_updateFinishedPrefix___rarg___closed__1;
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__4(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Task_Priority_default;
x_5 = lean_task_map(x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 4, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Task_Priority_default;
x_22 = lean_io_as_task(x_20, x_21, x_17);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_6, 0, x_27);
lean_ctor_set(x_22, 0, x_6);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_1, x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_6, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_6);
lean_dec(x_19);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
lean_dec(x_6);
lean_inc(x_38);
lean_inc(x_1);
x_39 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 4, 3);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_2);
lean_closure_set(x_39, 2, x_38);
x_40 = l_Task_Priority_default;
x_41 = lean_io_as_task(x_39, x_40, x_17);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_1, x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
lean_dec(x_1);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
return x_5;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync_step(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync_step___rarg), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = l_Task_Priority_default;
x_7 = lean_io_as_task(x_5, x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_1, x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_unfoldAsync(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_unfoldAsync___rarg), 4, 0);
return x_3;
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
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__2), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_9);
x_10 = lean_task_pure(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_task_pure(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_IO_AsyncList_waitAll___rarg(x_1, x_2, x_19, x_4);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1;
x_24 = l_Task_Priority_default;
x_25 = lean_task_map(x_23, x_22, x_24);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1;
x_29 = l_Task_Priority_default;
x_30 = lean_task_map(x_28, x_26, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
return x_8;
}
}
}
static lean_object* _init_l_IO_AsyncList_waitAll___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_AsyncList_getAll___rarg___closed__1;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_5);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_task_pure(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_IO_AsyncList_waitAll___rarg(x_1, x_2, x_6, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__1), 2, 1);
lean_closure_set(x_18, 0, x_5);
x_19 = l_Task_Priority_default;
x_20 = lean_task_map(x_18, x_17, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__1), 2, 1);
lean_closure_set(x_23, 0, x_5);
x_24 = l_Task_Priority_default;
x_25 = lean_task_map(x_23, x_21, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__3), 4, 2);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_2);
x_33 = l_Task_Priority_default;
x_34 = lean_io_bind_task(x_31, x_32, x_33, x_4);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__4), 2, 1);
lean_closure_set(x_37, 0, x_1);
x_38 = lean_task_map(x_37, x_36, x_33);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg___lambda__4), 2, 1);
lean_closure_set(x_41, 0, x_1);
x_42 = lean_task_map(x_41, x_39, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_IO_AsyncList_waitAll___rarg___closed__1;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_waitAll___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_task_pure(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_task_pure(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_IO_AsyncList_waitFind_x3f___rarg(x_1, x_2, x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1;
x_19 = l_Task_Priority_default;
x_20 = lean_task_map(x_18, x_17, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1;
x_24 = l_Task_Priority_default;
x_25 = lean_task_map(x_23, x_21, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
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
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_5);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_task_pure(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___rarg___lambda__1), 4, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
x_16 = l_Task_Priority_default;
x_17 = lean_io_bind_task(x_14, x_15, x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_2, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_coeErr___rarg(x_2, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
default: 
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = l_IO_AsyncList_waitFind_x3f___rarg___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_waitFind_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_waitFind_x3f___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_IO_AsyncList_updateFinishedPrefix___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_updateFinishedPrefix___rarg(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_IO_AsyncList_updateFinishedPrefix___rarg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = l_IO_AsyncList_updateFinishedPrefix___rarg(x_26, x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_30)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_30;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_39 = x_27;
} else {
 lean_dec_ref(x_27);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
case 1:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
x_42 = lean_io_has_finished(x_41, x_2);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_42);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_42, 1);
x_55 = lean_ctor_get(x_42, 0);
lean_dec(x_55);
x_56 = lean_task_get_own(x_41);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(2);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_42, 0, x_60);
return x_42;
}
else
{
lean_object* x_61; 
lean_free_object(x_42);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_1 = x_61;
x_2 = x_54;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_dec(x_42);
x_64 = lean_task_get_own(x_41);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(2);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_1 = x_70;
x_2 = x_63;
goto _start;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_41);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_42, 0);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_42);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
default: 
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_IO_AsyncList_updateFinishedPrefix___rarg___closed__1;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_2);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_updateFinishedPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_updateFinishedPrefix___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_finishedPrefix___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Server_AsyncList_0__IO_AsyncList_finishedPrefixAux___rarg(x_2, x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_finishedPrefix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_AsyncList_finishedPrefix___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_AsyncList_finishedPrefix___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_AsyncList_finishedPrefix___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_AsyncList(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_IO_AsyncList_instAppendAsyncList___closed__1 = _init_l_IO_AsyncList_instAppendAsyncList___closed__1();
lean_mark_persistent(l_IO_AsyncList_instAppendAsyncList___closed__1);
l_IO_AsyncList_instCoeListAsyncList___closed__1 = _init_l_IO_AsyncList_instCoeListAsyncList___closed__1();
lean_mark_persistent(l_IO_AsyncList_instCoeListAsyncList___closed__1);
l_IO_AsyncList_getAll___rarg___closed__1 = _init_l_IO_AsyncList_getAll___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_getAll___rarg___closed__1);
l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1 = _init_l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitAll___rarg___lambda__3___closed__1);
l_IO_AsyncList_waitAll___rarg___closed__1 = _init_l_IO_AsyncList_waitAll___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitAll___rarg___closed__1);
l_IO_AsyncList_waitFind_x3f___rarg___closed__1 = _init_l_IO_AsyncList_waitFind_x3f___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___rarg___closed__1);
l_IO_AsyncList_waitFind_x3f___rarg___closed__2 = _init_l_IO_AsyncList_waitFind_x3f___rarg___closed__2();
lean_mark_persistent(l_IO_AsyncList_waitFind_x3f___rarg___closed__2);
l_IO_AsyncList_updateFinishedPrefix___rarg___closed__1 = _init_l_IO_AsyncList_updateFinishedPrefix___rarg___closed__1();
lean_mark_persistent(l_IO_AsyncList_updateFinishedPrefix___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

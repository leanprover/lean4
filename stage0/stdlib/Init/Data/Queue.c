// Lean compiler output
// Module: Init.Data.Queue
// Imports: Init.Data.Array.Basic
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
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Queue_empty___closed__1;
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray___rarg(lean_object*);
static lean_object* l_Std_Queue_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object*);
static lean_object* _init_l_Std_Queue_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Queue_empty___closed__1;
return x_2;
}
}
static lean_object* _init_l_Std_Queue_instEmptyCollection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Queue_instEmptyCollection___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Queue_instEmptyCollection___closed__1;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_List_isEmpty___rarg(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Queue_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Queue_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Queue_enqueue___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_List_appendTR___rarg(x_1, x_4);
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
x_8 = l_List_appendTR___rarg(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Queue_enqueueAll___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = l_List_reverse___rarg(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_free_object(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_box(0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_box(0);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_List_reverse___rarg(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
 lean_ctor_set_tag(x_25, 0);
}
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_1, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 1);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_1);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_39 = x_2;
} else {
 lean_dec_ref(x_2);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
 lean_ctor_set_tag(x_41, 0);
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Queue_dequeue_x3f___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_mk(x_3);
x_5 = lean_array_mk(x_2);
x_6 = l_Array_reverse___rarg(x_5);
x_7 = l_Array_append___rarg(x_4, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Queue_toArray___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Queue(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Queue_empty___closed__1 = _init_l_Std_Queue_empty___closed__1();
lean_mark_persistent(l_Std_Queue_empty___closed__1);
l_Std_Queue_instEmptyCollection___closed__1 = _init_l_Std_Queue_instEmptyCollection___closed__1();
lean_mark_persistent(l_Std_Queue_instEmptyCollection___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

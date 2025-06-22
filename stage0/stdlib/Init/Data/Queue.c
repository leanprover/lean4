// Lean compiler output
// Module: Init.Data.Queue
// Imports: Init.Data.List.Control
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
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filterAuxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_empty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instEmptyCollection(lean_object*);
static lean_object* l_Std_Queue_empty___closed__0;
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object*, lean_object*);
static lean_object* l_Std_Queue_instEmptyCollection___closed__0;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object*, lean_object*);
static lean_object* _init_l_Std_Queue_empty___closed__0() {
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
x_2 = l_Std_Queue_empty___closed__0;
return x_2;
}
}
static lean_object* _init_l_Std_Queue_instEmptyCollection___closed__0() {
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
x_2 = l_Std_Queue_instEmptyCollection___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Queue_instEmptyCollection___closed__0;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_List_isEmpty___redArg(x_3);
if (x_4 == 0)
{
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_List_isEmpty___redArg(x_2);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Std_Queue_isEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Queue_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Queue_isEmpty___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_isEmpty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Queue_isEmpty(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueue___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_Queue_enqueue(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Queue_enqueue___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_List_appendTR___redArg(x_1, x_4);
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
x_8 = l_List_appendTR___redArg(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_enqueueAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Queue_enqueueAll___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object* x_1) {
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
x_6 = l_List_reverse___redArg(x_4);
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_2);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_List_reverse___redArg(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
 lean_ctor_set_tag(x_22, 0);
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 1);
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_36 = x_2;
} else {
 lean_dec_ref(x_2);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_35);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_dequeue_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Queue_dequeue_x3f___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray___redArg(lean_object* x_1) {
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
x_6 = l_Array_reverse___redArg(x_5);
x_7 = l_Array_append___redArg(x_4, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_toArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Queue_toArray___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_isEmpty___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = l_List_reverse___redArg(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_box(0);
x_9 = l_List_filterAuxM___redArg(x_2, x_3, x_4, x_8);
x_10 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 2, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_5);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__2), 6, 5);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_6);
lean_closure_set(x_9, 4, x_5);
x_10 = lean_box(0);
x_11 = l_List_filterAuxM___redArg(x_1, x_2, x_7, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Queue_filterM___redArg___lam__1), 2, 1);
lean_closure_set(x_12, 0, x_8);
lean_inc(x_5);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Queue_filterM___redArg(x_2, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Queue(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Queue_empty___closed__0 = _init_l_Std_Queue_empty___closed__0();
lean_mark_persistent(l_Std_Queue_empty___closed__0);
l_Std_Queue_instEmptyCollection___closed__0 = _init_l_Std_Queue_instEmptyCollection___closed__0();
lean_mark_persistent(l_Std_Queue_instEmptyCollection___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

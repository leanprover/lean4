// Lean compiler output
// Module: Init.Data.List.Instances
// Imports: Init.Data.List.Basic Init.Control.Alternative Init.Control.Monad
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
lean_object* l_List_map___main___at_List_Monad___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_List_Alternative___lambda__1(lean_object*);
lean_object* l_List_bind(lean_object*, lean_object*);
lean_object* l_List_Monad___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_Monad___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_List_Monad;
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
lean_object* l_List_Monad___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append(lean_object*);
lean_object* l_List_Monad___closed__8;
lean_object* l_List_Monad___closed__6;
lean_object* l_List_join___main___rarg(lean_object*);
lean_object* l_List_Alternative___closed__1;
lean_object* l_List_Monad___closed__10;
lean_object* l_List_Monad___closed__5;
lean_object* l_List_pure(lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__3(lean_object*, lean_object*);
lean_object* l_List_Alternative___closed__2;
lean_object* l_List_Monad___closed__9;
lean_object* l_List_map___main___at_List_Monad___spec__5___rarg(lean_object*, lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__1(lean_object*, lean_object*);
lean_object* l_List_Monad___closed__1;
lean_object* l_List_Monad___closed__3;
lean_object* l_List_Alternative;
lean_object* l_List_map___main___at_List_Monad___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_Monad___closed__7;
lean_object* l_List_Monad___closed__4;
lean_object* l_List_map___main___at_List_Monad___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_List_map(lean_object*, lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__2(lean_object*, lean_object*);
lean_object* l_List_Monad___closed__2;
lean_object* l_List_Alternative___closed__3;
lean_object* l_List_Monad___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__5(lean_object*, lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__4(lean_object*, lean_object*);
lean_object* l_List_map___main___at_List_Monad___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
lean_inc(x_1);
x_7 = l_List_map___main___at_List_Monad___spec__1___rarg(x_1, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_List_map___main___at_List_Monad___spec__1___rarg(x_1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_List_map___main___at_List_Monad___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_List_Monad___spec__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_map___main___at_List_Monad___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_map___main___rarg(x_5, x_1);
x_8 = l_List_map___main___at_List_Monad___spec__2___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
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
x_11 = l_List_map___main___rarg(x_9, x_1);
x_12 = l_List_map___main___at_List_Monad___spec__2___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_List_Monad___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_List_Monad___spec__2___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_map___main___at_List_Monad___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_1);
x_8 = l_List_map___main___at_List_Monad___spec__3___rarg(x_1, x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
lean_inc(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_map___main___at_List_Monad___spec__3___rarg(x_1, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_map___main___at_List_Monad___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_List_Monad___spec__3___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_map___main___at_List_Monad___spec__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___main___at_List_Monad___spec__3___rarg(x_5, x_1);
x_8 = l_List_join___main___rarg(x_7);
x_9 = l_List_map___main___at_List_Monad___spec__4___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_List_map___main___at_List_Monad___spec__3___rarg(x_10, x_1);
x_13 = l_List_join___main___rarg(x_12);
x_14 = l_List_map___main___at_List_Monad___spec__4___rarg(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_List_map___main___at_List_Monad___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_List_Monad___spec__4___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_map___main___at_List_Monad___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
lean_inc(x_1);
x_7 = l_List_map___main___at_List_Monad___spec__5___rarg(x_1, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_List_map___main___at_List_Monad___spec__5___rarg(x_1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* l_List_map___main___at_List_Monad___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_List_Monad___spec__5___rarg), 2, 0);
return x_3;
}
}
lean_object* l_List_Monad___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_map___main___at_List_Monad___spec__1___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_List_Monad___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_map___main___at_List_Monad___spec__2___rarg(x_4, x_3);
x_6 = l_List_join___main___rarg(x_5);
return x_6;
}
}
lean_object* l_List_Monad___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_map___main___at_List_Monad___spec__4___rarg(x_4, x_3);
x_6 = l_List_join___main___rarg(x_5);
return x_6;
}
}
lean_object* l_List_Monad___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_map___main___at_List_Monad___spec__5___rarg(x_4, x_3);
x_6 = l_List_join___main___rarg(x_5);
return x_6;
}
}
lean_object* _init_l_List_Monad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_map), 2, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_Monad___lambda__1), 4, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad___closed__1;
x_2 = l_List_Monad___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_List_Monad___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_pure), 1, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_Monad___lambda__2), 4, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_Monad___lambda__3), 4, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_Monad___lambda__4), 4, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_Monad___closed__3;
x_2 = l_List_Monad___closed__4;
x_3 = l_List_Monad___closed__5;
x_4 = l_List_Monad___closed__6;
x_5 = l_List_Monad___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_List_Monad___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_bind), 2, 0);
return x_1;
}
}
lean_object* _init_l_List_Monad___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad___closed__8;
x_2 = l_List_Monad___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_List_Monad() {
_start:
{
lean_object* x_1; 
x_1 = l_List_Monad___closed__10;
return x_1;
}
}
lean_object* l_List_Alternative___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* _init_l_List_Alternative___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_Alternative___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_List_Alternative___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_append), 1, 0);
return x_1;
}
}
lean_object* _init_l_List_Alternative___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_List_Monad;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_List_Alternative___closed__1;
x_4 = l_List_Alternative___closed__2;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_List_Alternative() {
_start:
{
lean_object* x_1; 
x_1 = l_List_Alternative___closed__3;
return x_1;
}
}
lean_object* initialize_Init_Data_List_Basic(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Control_Monad(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_List_Instances(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Monad(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_Monad___closed__1 = _init_l_List_Monad___closed__1();
lean_mark_persistent(l_List_Monad___closed__1);
l_List_Monad___closed__2 = _init_l_List_Monad___closed__2();
lean_mark_persistent(l_List_Monad___closed__2);
l_List_Monad___closed__3 = _init_l_List_Monad___closed__3();
lean_mark_persistent(l_List_Monad___closed__3);
l_List_Monad___closed__4 = _init_l_List_Monad___closed__4();
lean_mark_persistent(l_List_Monad___closed__4);
l_List_Monad___closed__5 = _init_l_List_Monad___closed__5();
lean_mark_persistent(l_List_Monad___closed__5);
l_List_Monad___closed__6 = _init_l_List_Monad___closed__6();
lean_mark_persistent(l_List_Monad___closed__6);
l_List_Monad___closed__7 = _init_l_List_Monad___closed__7();
lean_mark_persistent(l_List_Monad___closed__7);
l_List_Monad___closed__8 = _init_l_List_Monad___closed__8();
lean_mark_persistent(l_List_Monad___closed__8);
l_List_Monad___closed__9 = _init_l_List_Monad___closed__9();
lean_mark_persistent(l_List_Monad___closed__9);
l_List_Monad___closed__10 = _init_l_List_Monad___closed__10();
lean_mark_persistent(l_List_Monad___closed__10);
l_List_Monad = _init_l_List_Monad();
lean_mark_persistent(l_List_Monad);
l_List_Alternative___closed__1 = _init_l_List_Alternative___closed__1();
lean_mark_persistent(l_List_Alternative___closed__1);
l_List_Alternative___closed__2 = _init_l_List_Alternative___closed__2();
lean_mark_persistent(l_List_Alternative___closed__2);
l_List_Alternative___closed__3 = _init_l_List_Alternative___closed__3();
lean_mark_persistent(l_List_Alternative___closed__3);
l_List_Alternative = _init_l_List_Alternative();
lean_mark_persistent(l_List_Alternative);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

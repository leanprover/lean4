// Lean compiler output
// Module: init.data.list.instances
// Imports: init.data.list.basic init.control.alternative init.control.monad
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
obj* l_List_map___main___at_List_Monad___spec__3___rarg(obj*, obj*);
obj* l_List_Alternative___lambda__1(obj*);
obj* l_List_bind(obj*, obj*);
obj* l_List_Monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_List_Monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__2___rarg(obj*, obj*);
obj* l_List_Monad;
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_List_Monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_List_append(obj*);
obj* l_List_Monad___closed__8;
obj* l_List_Monad___closed__6;
obj* l_List_join___main___rarg(obj*);
obj* l_List_Alternative___closed__1;
obj* l_List_Monad___closed__10;
obj* l_List_Monad___closed__5;
obj* l_List_pure(obj*);
obj* l_List_map___main___at_List_Monad___spec__3(obj*, obj*);
obj* l_List_Alternative___closed__2;
obj* l_List_Monad___closed__9;
obj* l_List_map___main___at_List_Monad___spec__5___rarg(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__1(obj*, obj*);
obj* l_List_Monad___closed__1;
obj* l_List_Monad___closed__3;
obj* l_List_Alternative;
obj* l_List_map___main___at_List_Monad___spec__1___rarg(obj*, obj*);
obj* l_List_Monad___closed__7;
obj* l_List_Monad___closed__4;
obj* l_List_map___main___at_List_Monad___spec__4___rarg(obj*, obj*);
obj* l_List_map(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__2(obj*, obj*);
obj* l_List_Monad___closed__2;
obj* l_List_Alternative___closed__3;
obj* l_List_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__5(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__4(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 0);
lean::dec(x_6);
lean::inc(x_1);
x_7 = l_List_map___main___at_List_Monad___spec__1___rarg(x_1, x_5);
lean::cnstr_set(x_2, 1, x_7);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
x_9 = l_List_map___main___at_List_Monad___spec__1___rarg(x_1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
}
obj* l_List_map___main___at_List_Monad___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_List_map___main___at_List_Monad___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = l_List_map___main___rarg(x_5, x_1);
x_8 = l_List_map___main___at_List_Monad___spec__2___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = l_List_map___main___rarg(x_9, x_1);
x_12 = l_List_map___main___at_List_Monad___spec__2___rarg(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_List_map___main___at_List_Monad___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__2___rarg), 2, 0);
return x_3;
}
}
obj* l_List_map___main___at_List_Monad___spec__3___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 0);
lean::dec(x_6);
x_7 = lean::box(0);
lean::inc(x_1);
lean::cnstr_set(x_2, 1, x_7);
lean::cnstr_set(x_2, 0, x_1);
x_8 = l_List_map___main___at_List_Monad___spec__3___rarg(x_1, x_5);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::box(0);
lean::inc(x_1);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_List_map___main___at_List_Monad___spec__3___rarg(x_1, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_List_map___main___at_List_Monad___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__3___rarg), 2, 0);
return x_3;
}
}
obj* l_List_map___main___at_List_Monad___spec__4___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = l_List_map___main___at_List_Monad___spec__3___rarg(x_5, x_1);
x_8 = l_List_join___main___rarg(x_7);
x_9 = l_List_map___main___at_List_Monad___spec__4___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_9);
lean::cnstr_set(x_2, 0, x_8);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
x_12 = l_List_map___main___at_List_Monad___spec__3___rarg(x_10, x_1);
x_13 = l_List_join___main___rarg(x_12);
x_14 = l_List_map___main___at_List_Monad___spec__4___rarg(x_1, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_List_map___main___at_List_Monad___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__4___rarg), 2, 0);
return x_3;
}
}
obj* l_List_map___main___at_List_Monad___spec__5___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 0);
lean::dec(x_6);
lean::inc(x_1);
x_7 = l_List_map___main___at_List_Monad___spec__5___rarg(x_1, x_5);
lean::cnstr_set(x_2, 1, x_7);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
x_9 = l_List_map___main___at_List_Monad___spec__5___rarg(x_1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
}
obj* l_List_map___main___at_List_Monad___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__5___rarg), 2, 0);
return x_3;
}
}
obj* l_List_Monad___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_map___main___at_List_Monad___spec__1___rarg(x_3, x_4);
return x_5;
}
}
obj* l_List_Monad___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_List_map___main___at_List_Monad___spec__2___rarg(x_4, x_3);
x_6 = l_List_join___main___rarg(x_5);
return x_6;
}
}
obj* l_List_Monad___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_List_map___main___at_List_Monad___spec__4___rarg(x_4, x_3);
x_6 = l_List_join___main___rarg(x_5);
return x_6;
}
}
obj* l_List_Monad___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_List_map___main___at_List_Monad___spec__5___rarg(x_4, x_3);
x_6 = l_List_join___main___rarg(x_5);
return x_6;
}
}
obj* _init_l_List_Monad___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map), 2, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__1), 4, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_List_Monad___closed__1;
x_2 = l_List_Monad___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_List_Monad___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_pure), 1, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__2), 4, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__3), 4, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__4), 4, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_List_Monad___closed__3;
x_2 = l_List_Monad___closed__4;
x_3 = l_List_Monad___closed__5;
x_4 = l_List_Monad___closed__6;
x_5 = l_List_Monad___closed__7;
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
lean::cnstr_set(x_6, 4, x_5);
return x_6;
}
}
obj* _init_l_List_Monad___closed__9() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_bind), 2, 0);
return x_1;
}
}
obj* _init_l_List_Monad___closed__10() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_List_Monad___closed__8;
x_2 = l_List_Monad___closed__9;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_List_Monad() {
_start:
{
obj* x_1; 
x_1 = l_List_Monad___closed__10;
return x_1;
}
}
obj* l_List_Alternative___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* _init_l_List_Alternative___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Alternative___lambda__1), 1, 0);
return x_1;
}
}
obj* _init_l_List_Alternative___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_append), 1, 0);
return x_1;
}
}
obj* _init_l_List_Alternative___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_List_Monad;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_List_Alternative___closed__1;
x_4 = l_List_Alternative___closed__2;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
}
obj* _init_l_List_Alternative() {
_start:
{
obj* x_1; 
x_1 = l_List_Alternative___closed__3;
return x_1;
}
}
obj* initialize_init_data_list_basic(obj*);
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_control_monad(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_list_instances(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (lean::io_result_is_error(w)) return w;
l_List_Monad___closed__1 = _init_l_List_Monad___closed__1();
lean::mark_persistent(l_List_Monad___closed__1);
l_List_Monad___closed__2 = _init_l_List_Monad___closed__2();
lean::mark_persistent(l_List_Monad___closed__2);
l_List_Monad___closed__3 = _init_l_List_Monad___closed__3();
lean::mark_persistent(l_List_Monad___closed__3);
l_List_Monad___closed__4 = _init_l_List_Monad___closed__4();
lean::mark_persistent(l_List_Monad___closed__4);
l_List_Monad___closed__5 = _init_l_List_Monad___closed__5();
lean::mark_persistent(l_List_Monad___closed__5);
l_List_Monad___closed__6 = _init_l_List_Monad___closed__6();
lean::mark_persistent(l_List_Monad___closed__6);
l_List_Monad___closed__7 = _init_l_List_Monad___closed__7();
lean::mark_persistent(l_List_Monad___closed__7);
l_List_Monad___closed__8 = _init_l_List_Monad___closed__8();
lean::mark_persistent(l_List_Monad___closed__8);
l_List_Monad___closed__9 = _init_l_List_Monad___closed__9();
lean::mark_persistent(l_List_Monad___closed__9);
l_List_Monad___closed__10 = _init_l_List_Monad___closed__10();
lean::mark_persistent(l_List_Monad___closed__10);
l_List_Monad = _init_l_List_Monad();
lean::mark_persistent(l_List_Monad);
l_List_Alternative___closed__1 = _init_l_List_Alternative___closed__1();
lean::mark_persistent(l_List_Alternative___closed__1);
l_List_Alternative___closed__2 = _init_l_List_Alternative___closed__2();
lean::mark_persistent(l_List_Alternative___closed__2);
l_List_Alternative___closed__3 = _init_l_List_Alternative___closed__3();
lean::mark_persistent(l_List_Alternative___closed__3);
l_List_Alternative = _init_l_List_Alternative();
lean::mark_persistent(l_List_Alternative);
return w;
}
}

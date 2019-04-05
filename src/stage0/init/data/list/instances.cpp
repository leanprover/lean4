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
obj* l_List_map___main___at_List_Monad___spec__3___rarg(obj*, obj*);
obj* l_List_Alternative___lambda__1(obj*);
obj* l_List_Monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_List_Monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__2___rarg(obj*, obj*);
obj* l_List_Monad;
obj* l_List_map___main___rarg(obj*, obj*);
obj* l_List_Monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_List_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___boxed(obj*, obj*);
obj* l_List_join___main___rarg(obj*);
obj* l_List_map___main___at_List_Monad___spec__2___boxed(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__3___boxed(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__3(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__4___boxed(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__5___boxed(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__5___rarg(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__1(obj*, obj*);
obj* l_List_Monad___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_List_Alternative;
obj* l_List_map___main___at_List_Monad___spec__1___rarg(obj*, obj*);
obj* l_List_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__4___rarg(obj*, obj*);
obj* l_List_append___boxed(obj*);
obj* l_List_map___main___at_List_Monad___spec__2(obj*, obj*);
obj* l_List_bind___boxed(obj*, obj*);
obj* l_List_Monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_List_pure___boxed(obj*);
obj* l_List_Alternative___lambda__1___boxed(obj*);
obj* l_List_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__5(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__4(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__1___boxed(obj*, obj*);
obj* l_List_map___main___at_List_Monad___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
lean::inc(x_0);
x_8 = l_List_map___main___at_List_Monad___spec__1___rarg(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_List_map___main___at_List_Monad___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
lean::inc(x_0);
x_10 = l_List_map___main___rarg(x_4, x_0);
x_11 = l_List_map___main___at_List_Monad___spec__2___rarg(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_List_map___main___at_List_Monad___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
lean::inc(x_0);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_List_map___main___at_List_Monad___spec__3___rarg(x_0, x_4);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* l_List_map___main___at_List_Monad___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__3___rarg), 2, 0);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
lean::inc(x_0);
x_10 = l_List_map___main___at_List_Monad___spec__3___rarg(x_4, x_0);
x_11 = l_List_join___main___rarg(x_10);
x_12 = l_List_map___main___at_List_Monad___spec__4___rarg(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_List_map___main___at_List_Monad___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__4___rarg), 2, 0);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
lean::inc(x_0);
x_8 = l_List_map___main___at_List_Monad___spec__5___rarg(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_List_map___main___at_List_Monad___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_List_Monad___spec__5___rarg), 2, 0);
return x_2;
}
}
obj* l_List_Monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_map___main___at_List_Monad___spec__1___rarg(x_2, x_3);
return x_4;
}
}
obj* l_List_Monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_List_map___main___at_List_Monad___spec__2___rarg(x_3, x_2);
x_5 = l_List_join___main___rarg(x_4);
return x_5;
}
}
obj* l_List_Monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_List_map___main___at_List_Monad___spec__4___rarg(x_3, x_2);
x_5 = l_List_join___main___rarg(x_4);
return x_5;
}
}
obj* l_List_Monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_List_map___main___at_List_Monad___spec__5___rarg(x_3, x_2);
x_5 = l_List_join___main___rarg(x_4);
return x_5;
}
}
obj* _init_l_List_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__1___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_pure___boxed), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__2___boxed), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__3___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Monad___lambda__4___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_List_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_List_map___main___at_List_Monad___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_List_Monad___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_List_Monad___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_List_Monad___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_List_Monad___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_List_Monad___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_map___main___at_List_Monad___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_Monad___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_Monad___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_Monad___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_Monad___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_Monad___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_Monad___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_Monad___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_List_Monad___lambda__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_Alternative___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_List_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_List_Monad;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_List_append___boxed), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_List_Alternative___lambda__1___boxed), 1, 0);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 2, x_5);
return x_6;
}
}
obj* l_List_Alternative___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_Alternative___lambda__1(x_0);
lean::dec(x_0);
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
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
 l_List_Monad = _init_l_List_Monad();
lean::mark_persistent(l_List_Monad);
 l_List_Alternative = _init_l_List_Alternative();
lean::mark_persistent(l_List_Alternative);
return w;
}

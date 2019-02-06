// Lean compiler output
// Module: init.data.list.instances
// Imports: init.data.list.basic init.control.alternative init.control.monad
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_list_map___main___at_list_monad___spec__1___rarg(obj*, obj*);
obj* l_list_alternative___lambda__2(obj*, obj*, obj*, obj*);
obj* l_list_map___main___rarg(obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__5(obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__3___rarg(obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__1(obj*, obj*);
obj* l_list_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__3(obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__4(obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__1(obj*, obj*);
obj* l_list_join___main___rarg(obj*);
obj* l_list_map___main___at_list_alternative___spec__2(obj*, obj*);
obj* l_list_alternative;
obj* l_list_map___main___at_list_alternative___spec__2___rarg(obj*, obj*);
obj* l_list_monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__4(obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__3(obj*, obj*);
obj* l_list_ret(obj*);
obj* l_list_map___main___at_list_monad___spec__2(obj*, obj*);
obj* l_list_alternative___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_alternative___lambda__3(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__1___rarg(obj*, obj*);
obj* l_list_append(obj*);
obj* l_list_alternative___lambda__5(obj*);
obj* l_list_map___main___at_list_monad___spec__4___rarg(obj*, obj*);
obj* l_list_alternative___lambda__4(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__2___rarg(obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__5___rarg(obj*, obj*);
obj* l_list_map(obj*, obj*);
obj* l_list_monad___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_bind(obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__5___rarg(obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__3___rarg(obj*, obj*);
obj* l_list_map___main___at_list_alternative___spec__4___rarg(obj*, obj*);
obj* l_list_monad;
obj* l_list_map___main___at_list_monad___spec__5(obj*, obj*);
obj* l_list_monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_list_monad___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
lean::inc(x_0);
x_9 = l_list_map___main___at_list_monad___spec__1___rarg(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_list_monad___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_monad___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_monad___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = l_list_map___main___rarg(x_5, x_0);
x_12 = l_list_map___main___at_list_monad___spec__2___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_list_map___main___at_list_monad___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_monad___spec__2___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_monad___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::box(0);
lean::inc(x_0);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_list_map___main___at_list_monad___spec__3___rarg(x_0, x_5);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_list_map___main___at_list_monad___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_monad___spec__3___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_monad___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = l_list_map___main___at_list_monad___spec__3___rarg(x_5, x_0);
x_12 = l_list_join___main___rarg(x_11);
x_13 = l_list_map___main___at_list_monad___spec__4___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_list_monad___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_monad___spec__4___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_monad___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
lean::inc(x_0);
x_9 = l_list_map___main___at_list_monad___spec__5___rarg(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_list_monad___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_monad___spec__5___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_list_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_monad___lambda__1), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_list_ret), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_monad___lambda__2), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_list_monad___lambda__3), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_monad___lambda__4), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_list_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_list_monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_monad___spec__1___rarg(x_2, x_3);
return x_6;
}
}
obj* l_list_monad___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_monad___spec__2___rarg(x_3, x_2);
x_7 = l_list_join___main___rarg(x_6);
return x_7;
}
}
obj* l_list_monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_monad___spec__4___rarg(x_3, x_2);
x_7 = l_list_join___main___rarg(x_6);
return x_7;
}
}
obj* l_list_monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_monad___spec__5___rarg(x_3, x_2);
x_7 = l_list_join___main___rarg(x_6);
return x_7;
}
}
obj* l_list_map___main___at_list_alternative___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
lean::inc(x_0);
x_9 = l_list_map___main___at_list_alternative___spec__1___rarg(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_list_alternative___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_alternative___spec__1___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_alternative___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = l_list_map___main___rarg(x_5, x_0);
x_12 = l_list_map___main___at_list_alternative___spec__2___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_list_map___main___at_list_alternative___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_alternative___spec__2___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_alternative___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::box(0);
lean::inc(x_0);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_8);
x_11 = l_list_map___main___at_list_alternative___spec__3___rarg(x_0, x_5);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
obj* l_list_map___main___at_list_alternative___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_alternative___spec__3___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_alternative___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = l_list_map___main___at_list_alternative___spec__3___rarg(x_5, x_0);
x_12 = l_list_join___main___rarg(x_11);
x_13 = l_list_map___main___at_list_alternative___spec__4___rarg(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_list_map___main___at_list_alternative___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_alternative___spec__4___rarg), 2, 0);
return x_4;
}
}
obj* l_list_map___main___at_list_alternative___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
lean::inc(x_0);
x_9 = l_list_map___main___at_list_alternative___spec__5___rarg(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* l_list_map___main___at_list_alternative___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_list_alternative___spec__5___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_list_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_alternative___lambda__1), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_list_ret), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_alternative___lambda__2), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_list_alternative___lambda__3), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_alternative___lambda__4), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_list_append), 1, 0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_list_alternative___lambda__5), 1, 0);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_9);
return x_10;
}
}
obj* l_list_alternative___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_alternative___spec__1___rarg(x_2, x_3);
return x_6;
}
}
obj* l_list_alternative___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_alternative___spec__2___rarg(x_3, x_2);
x_7 = l_list_join___main___rarg(x_6);
return x_7;
}
}
obj* l_list_alternative___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_alternative___spec__4___rarg(x_3, x_2);
x_7 = l_list_join___main___rarg(x_6);
return x_7;
}
}
obj* l_list_alternative___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_list_map___main___at_list_alternative___spec__5___rarg(x_3, x_2);
x_7 = l_list_join___main___rarg(x_6);
return x_7;
}
}
obj* l_list_alternative___lambda__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
}
void initialize_init_data_list_basic();
void initialize_init_control_alternative();
void initialize_init_control_monad();
static bool _G_initialized = false;
void initialize_init_data_list_instances() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_list_basic();
 initialize_init_control_alternative();
 initialize_init_control_monad();
 l_list_monad = _init_l_list_monad();
 l_list_alternative = _init_l_list_alternative();
}

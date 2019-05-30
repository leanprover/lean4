// Lean compiler output
// Module: init.data.option.basic
// Imports: init.core init.control.monad init.control.alternative init.coe
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
obj* l_Option_isNone___main(obj*);
obj* l_Option_get___main___rarg___boxed(obj*, obj*);
obj* l_Option_isSome___main(obj*);
obj* l_Option_get___main___rarg(obj*, obj*);
obj* l_Option_Monad___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Option_Alternative;
uint8 l_Option_isSome___main___rarg(obj*);
obj* l_Option_Monad___lambda__4(obj*, obj*, obj*, obj*);
obj* l_Option_getOrElse___rarg___boxed(obj*, obj*);
obj* l_Option_toBool___main___rarg___boxed(obj*);
obj* l_Option_toMonad___main___boxed(obj*);
obj* l_Option_DecidableEq___rarg___boxed(obj*, obj*, obj*);
obj* l_Option_bind___main(obj*, obj*);
obj* l_Option_Monad;
obj* l_Option_get___rarg___boxed(obj*, obj*);
obj* l_Option_HasLess___boxed(obj*, obj*);
obj* l_Option_Monad___lambda__5(obj*, obj*, obj*, obj*);
obj* l_Option_decidableRelLt___boxed(obj*, obj*);
obj* l_Option_Monad___lambda__2(obj*, obj*);
obj* l_Option_bind___rarg(obj*, obj*);
obj* l_Option_isSome___main___rarg___boxed(obj*);
obj* l_Option_Monad___lambda__5___boxed(obj*, obj*, obj*, obj*);
obj* l_Option_isNone___rarg___boxed(obj*);
obj* l_Option_isNone___main___rarg___boxed(obj*);
obj* l_Option_getOrElse___main___rarg___boxed(obj*, obj*);
obj* l_Option_toMonad___main___rarg(obj*, obj*, obj*);
obj* l_Option_toMonad___boxed(obj*, obj*);
obj* l_Option_map___rarg(obj*, obj*);
obj* l_Option_orelse___rarg___boxed(obj*, obj*);
obj* l_Option_map(obj*, obj*);
obj* l_Option_Monad___lambda__1(obj*, obj*, obj*, obj*);
uint8 l_Option_toBool___rarg(obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Option_toMonad___rarg(obj*, obj*, obj*);
uint8 l_Option_toBool___main___rarg(obj*);
obj* l_Option_toMonad___main(obj*);
obj* l_Option_HasLess(obj*, obj*);
obj* l_Option_orelse___main___rarg(obj*, obj*);
obj* l_Option_Alternative___lambda__1(obj*);
uint8 l_Option_DecidableEq___rarg(obj*, obj*, obj*);
obj* l_Option_Inhabited(obj*);
obj* l_Option_decidableRelLt___main___rarg(obj*, obj*, obj*);
obj* l_Option_toBool___main(obj*);
obj* l_Option_toBool___rarg___boxed(obj*);
obj* l_Option_get(obj*);
obj* l_Option_bind___main___rarg(obj*, obj*);
obj* l_Option_Alternative___lambda__2(obj*, obj*, obj*);
obj* l_Option_isSome___rarg___boxed(obj*);
obj* l_Option_orelse(obj*);
obj* l_Option_getOrElse___main(obj*);
obj* l_Option_bind(obj*, obj*);
obj* l_Option_get___main(obj*);
obj* l_Option_getOrElse(obj*);
uint8 l_Option_isNone___main___rarg(obj*);
obj* l_Option_decidableRelLt___rarg(obj*, obj*, obj*);
obj* l_Option_isNone(obj*);
obj* l_Option_orelse___main(obj*);
obj* l_Option_orelse___main___rarg___boxed(obj*, obj*);
obj* l_Option_orelse___rarg(obj*, obj*);
obj* l_Option_isSome(obj*);
obj* l_Option_decidableRelLt___main___boxed(obj*, obj*);
obj* l_Option_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Option_Alternative___lambda__2___boxed(obj*, obj*, obj*);
obj* l_Option_decidableRelLt___main(obj*, obj*);
obj* l_Option_toMonad(obj*, obj*);
obj* l_Option_DecidableEq(obj*);
obj* l_Option_decidableRelLt(obj*, obj*);
obj* l_Option_getOrElse___rarg(obj*, obj*);
obj* l_Option_get___rarg(obj*, obj*);
uint8 l_Option_isSome___rarg(obj*);
obj* l_Option_toBool(obj*);
uint8 l_Option_isNone___rarg(obj*);
obj* l_Option_toMonad___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_4, lean::box(0));
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_6);
return x_9;
}
}
}
obj* l_Option_toMonad___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Option_toMonad___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_toMonad___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_toMonad___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_toMonad___main___rarg(x_1, lean::box(0), x_3);
return x_4;
}
}
obj* l_Option_toMonad(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___rarg), 3, 0);
return x_3;
}
}
obj* l_Option_toMonad___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_toMonad(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_getOrElse___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Option_getOrElse___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_getOrElse___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_getOrElse___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_getOrElse___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Option_getOrElse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_getOrElse___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_getOrElse___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_getOrElse___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_get___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Option_get___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_get___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_get___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_get___main___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_get___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Option_get(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_get___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_get___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_get___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Option_toBool___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Option_toBool___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toBool___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Option_toBool___main___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Option_toBool___main___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Option_toBool___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Option_toBool(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toBool___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Option_toBool___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Option_toBool___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Option_isSome___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Option_isSome___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isSome___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Option_isSome___main___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Option_isSome___main___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Option_isSome___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* l_Option_isSome(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isSome___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Option_isSome___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Option_isSome___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Option_isNone___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_Option_isNone___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isNone___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Option_isNone___main___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Option_isNone___main___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Option_isNone___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_Option_isNone(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isNone___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Option_isNone___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Option_isNone___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Option_bind___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
}
obj* l_Option_bind___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_bind___main___rarg), 2, 0);
return x_3;
}
}
obj* l_Option_bind___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
}
obj* l_Option_bind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_bind___rarg), 2, 0);
return x_3;
}
}
obj* l_Option_map___rarg(obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::apply_1(x_1, x_5);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_Option_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_map___rarg), 2, 0);
return x_3;
}
}
obj* l_Option_Monad___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::box(0);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; 
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
else
{
obj* x_8; 
lean::dec(x_4);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
return x_8;
}
}
}
}
obj* l_Option_Monad___lambda__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Option_Monad___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_4);
x_5 = lean::box(0);
return x_5;
}
else
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::apply_1(x_7, x_9);
lean::cnstr_set(x_4, 0, x_10);
return x_4;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::apply_1(x_7, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
}
}
obj* l_Option_Monad___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_4);
x_5 = lean::box(0);
return x_5;
}
else
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
else
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_4);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
}
}
obj* l_Option_Monad___lambda__5(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
lean::inc(x_4);
return x_4;
}
}
}
obj* _init_l_Option_Monad() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_map), 2, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__1), 4, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__2), 2, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__3), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__4___boxed), 4, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__5___boxed), 4, 0);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_6);
lean::cnstr_set(x_8, 4, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_bind), 2, 0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_Option_Monad___lambda__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Option_Monad___lambda__4(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Option_Monad___lambda__5___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Option_Monad___lambda__5(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Option_orelse___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Option_orelse___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_orelse___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_orelse___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_orelse___main___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_orelse___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Option_orelse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_orelse___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_orelse___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_orelse___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_Alternative___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Option_Alternative___lambda__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_3);
return x_3;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* _init_l_Option_Alternative() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Option_Monad;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Alternative___lambda__1), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Alternative___lambda__2___boxed), 3, 0);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
}
obj* l_Option_Alternative___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_Alternative___lambda__2(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Option_decidableRelLt___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
uint8 x_6; obj* x_7; 
lean::dec(x_3);
x_6 = 1;
x_7 = lean::box(x_6);
return x_7;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_8; obj* x_9; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = 0;
x_9 = lean::box(x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_12 = lean::apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
obj* l_Option_decidableRelLt___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_decidableRelLt___main___rarg), 3, 0);
return x_3;
}
}
obj* l_Option_decidableRelLt___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_decidableRelLt___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Option_decidableRelLt___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_decidableRelLt___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Option_decidableRelLt(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_decidableRelLt___rarg), 3, 0);
return x_3;
}
}
obj* l_Option_decidableRelLt___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_decidableRelLt(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Option_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
uint8 l_Option_DecidableEq___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
lean::dec(x_3);
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_6; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::apply_2(x_1, x_7, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
}
}
}
obj* l_Option_DecidableEq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_DecidableEq___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Option_DecidableEq___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Option_DecidableEq___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Option_HasLess(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Option_HasLess___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_HasLess(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_core(obj*);
obj* initialize_init_control_monad(obj*);
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_coe(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_option_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (io_result_is_error(w)) return w;
l_Option_Monad = _init_l_Option_Monad();
lean::mark_persistent(l_Option_Monad);
l_Option_Alternative = _init_l_Option_Alternative();
lean::mark_persistent(l_Option_Alternative);
return w;
}

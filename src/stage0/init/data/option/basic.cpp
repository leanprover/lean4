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
obj* l_Option_Monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Option_bind___main___boxed(obj*, obj*);
obj* l_Option_orelse___main___boxed(obj*);
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
obj* l_Option_orelse___boxed(obj*);
obj* l_Option_isNone___rarg___boxed(obj*);
obj* l_Option_isNone___main___rarg___boxed(obj*);
obj* l_Option_Monad___lambda__2___boxed(obj*, obj*);
obj* l_Option_map___boxed(obj*, obj*);
obj* l_Option_getOrElse___main___rarg___boxed(obj*, obj*);
obj* l_Option_toMonad___main___rarg(obj*, obj*, obj*);
obj* l_Option_Monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Option_toBool___boxed(obj*);
obj* l_Option_toBool___main___boxed(obj*);
obj* l_Option_toMonad___boxed(obj*, obj*);
obj* l_Option_map___rarg(obj*, obj*);
obj* l_Option_orelse___rarg___boxed(obj*, obj*);
obj* l_Option_isNone___boxed(obj*);
obj* l_Option_map(obj*, obj*);
obj* l_Option_Monad___lambda__1(obj*, obj*, obj*, obj*);
uint8 l_Option_toBool___rarg(obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l_Option_get___main___boxed(obj*);
obj* l_Option_toMonad___rarg(obj*, obj*, obj*);
obj* l_Option_DecidableEq___boxed(obj*);
obj* l_Option_toMonad___rarg___boxed(obj*, obj*, obj*);
uint8 l_Option_toBool___main___rarg(obj*);
obj* l_Option_toMonad___main(obj*);
obj* l_Option_HasLess(obj*, obj*);
obj* l_Option_orelse___main___rarg(obj*, obj*);
obj* l_Option_isSome___main___boxed(obj*);
obj* l_Option_Alternative___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Option_Alternative___lambda__1(obj*, obj*, obj*);
uint8 l_Option_DecidableEq___rarg(obj*, obj*, obj*);
obj* l_Option_Inhabited___boxed(obj*);
obj* l_Option_Inhabited(obj*);
obj* l_Option_decidableRelLt___main___rarg(obj*, obj*, obj*);
obj* l_Option_toBool___main(obj*);
obj* l_Option_toMonad___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Option_toBool___rarg___boxed(obj*);
obj* l_Option_get(obj*);
obj* l_Option_getOrElse___boxed(obj*);
obj* l_Option_bind___main___rarg(obj*, obj*);
obj* l_Option_Alternative___lambda__2(obj*);
obj* l_Option_isSome___rarg___boxed(obj*);
obj* l_Option_orelse(obj*);
obj* l_Option_getOrElse___main(obj*);
obj* l_Option_bind(obj*, obj*);
obj* l_Option_get___main(obj*);
obj* l_Option_getOrElse(obj*);
uint8 l_Option_isNone___main___rarg(obj*);
obj* l_Option_isSome___boxed(obj*);
obj* l_Option_decidableRelLt___rarg(obj*, obj*, obj*);
obj* l_Option_isNone(obj*);
obj* l_Option_orelse___main(obj*);
obj* l_Option_orelse___main___rarg___boxed(obj*, obj*);
obj* l_Option_orelse___rarg(obj*, obj*);
obj* l_Option_isNone___main___boxed(obj*);
obj* l_Option_isSome(obj*);
obj* l_Option_decidableRelLt___main___boxed(obj*, obj*);
obj* l_Option_Monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Option_Alternative___lambda__2___boxed(obj*);
obj* l_Option_getOrElse___main___boxed(obj*);
obj* l_Option_decidableRelLt___main(obj*, obj*);
obj* l_Option_toMonad(obj*, obj*);
obj* l_Option_DecidableEq(obj*);
obj* l_Option_decidableRelLt(obj*, obj*);
obj* l_Option_getOrElse___rarg(obj*, obj*);
obj* l_Option_get___rarg(obj*, obj*);
uint8 l_Option_isSome___rarg(obj*);
obj* l_Option_toBool(obj*);
obj* l_Option_bind___boxed(obj*, obj*);
uint8 l_Option_isNone___rarg(obj*);
obj* l_Option_get___boxed(obj*);
obj* l_Option_toMonad___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::apply_1(x_3, lean::box(0));
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), x_7);
return x_16;
}
}
}
obj* l_Option_toMonad___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Option_toMonad___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_toMonad___main___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_toMonad___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_toMonad___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_toMonad___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_toMonad___main___rarg(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_Option_toMonad(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Option_toMonad___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_toMonad___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_toMonad___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_toMonad(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_getOrElse___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Option_getOrElse___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_getOrElse___main___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_getOrElse___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_getOrElse___main___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_getOrElse___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_getOrElse___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_getOrElse___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Option_getOrElse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_getOrElse___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_getOrElse___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_getOrElse___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_getOrElse___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_getOrElse(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_get___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
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
obj* l_Option_get___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_get___main___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_get___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_get___main___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_get___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_get___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_get___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
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
obj* l_Option_get(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_get___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_get___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_get___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_get___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_get(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_toBool___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Option_toBool___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toBool___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Option_toBool___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Option_toBool___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_toBool___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_toBool___main(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_toBool___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Option_toBool(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toBool___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Option_toBool___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Option_toBool___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_toBool___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_toBool(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_isSome___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Option_isSome___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isSome___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Option_isSome___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Option_isSome___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_isSome___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_isSome___main(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_isSome___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Option_isSome(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isSome___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Option_isSome___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Option_isSome___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_isSome___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_isSome(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_isNone___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_Option_isNone___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isNone___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Option_isNone___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Option_isNone___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_isNone___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_isNone___main(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_isNone___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_Option_isNone(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_isNone___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Option_isNone___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Option_isNone___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_isNone___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_isNone(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_bind___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::apply_1(x_1, x_4);
return x_7;
}
}
}
obj* l_Option_bind___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_bind___main___rarg), 2, 0);
return x_2;
}
}
obj* l_Option_bind___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_bind___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_bind___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::apply_1(x_1, x_4);
return x_7;
}
}
}
obj* l_Option_bind(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_bind___rarg), 2, 0);
return x_2;
}
}
obj* l_Option_bind___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_bind(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_map___rarg(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
}
obj* l_Option_map(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_map___rarg), 2, 0);
return x_2;
}
}
obj* l_Option_map___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_map(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_Monad___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_6 = x_3;
} else {
 lean::dec(x_3);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_2);
return x_7;
}
}
}
obj* l_Option_Monad___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Option_Monad___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::box(0);
return x_5;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_13 = x_3;
} else {
 lean::inc(x_11);
 lean::dec(x_3);
 x_13 = lean::box(0);
}
x_14 = lean::apply_1(x_8, x_11);
if (lean::is_scalar(x_13)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_13;
}
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
}
}
}
obj* l_Option_Monad___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::box(0);
return x_5;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_12; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
if (lean::is_scalar(x_8)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_8;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
}
}
}
obj* l_Option_Monad___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
lean::inc(x_3);
return x_3;
}
}
}
obj* _init_l_Option_Monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__1___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__2___boxed), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__3___boxed), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__4___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__5___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Option_Monad___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_Monad___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Option_Monad___lambda__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_Monad___lambda__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Option_Monad___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_Monad___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Option_Monad___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_Monad___lambda__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Option_Monad___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_Monad___lambda__5(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Option_orelse___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l_Option_orelse___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_orelse___main___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_orelse___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_orelse___main___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_orelse___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_orelse___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_orelse___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l_Option_orelse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_orelse___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_orelse___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_orelse___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_orelse___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_orelse(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_Alternative___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_Option_Alternative___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Option_Alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_map___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__1___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__2___boxed), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__3___boxed), 4, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__4___boxed), 4, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Monad___lambda__5___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Alternative___lambda__1___boxed), 3, 0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_Alternative___lambda__2___boxed), 1, 0);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_9);
return x_10;
}
}
obj* l_Option_Alternative___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_Alternative___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Option_Alternative___lambda__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_Alternative___lambda__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_decidableRelLt___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
uint8 x_7; obj* x_8; 
lean::dec(x_2);
x_7 = 1;
x_8 = lean::box(x_7);
return x_8;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_11; obj* x_12; 
lean::dec(x_1);
lean::dec(x_0);
x_11 = 0;
x_12 = lean::box(x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
lean::dec(x_2);
x_19 = lean::apply_2(x_0, x_13, x_16);
return x_19;
}
}
}
}
obj* l_Option_decidableRelLt___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_decidableRelLt___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Option_decidableRelLt___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_decidableRelLt___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_decidableRelLt___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Option_decidableRelLt___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Option_decidableRelLt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_decidableRelLt___rarg), 3, 0);
return x_2;
}
}
obj* l_Option_decidableRelLt___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_decidableRelLt(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Option_Inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Option_Inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_Inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Option_DecidableEq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_2);
x_6 = 0;
return x_6;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = 0;
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; uint8 x_17; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::apply_2(x_0, x_10, x_13);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
uint8 x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
}
}
}
}
obj* l_Option_DecidableEq(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_DecidableEq___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Option_DecidableEq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Option_DecidableEq___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Option_DecidableEq___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_DecidableEq(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_HasLess(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Option_HasLess___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Option_HasLess(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
 l_Option_Monad = _init_l_Option_Monad();
lean::mark_persistent(l_Option_Monad);
 l_Option_Alternative = _init_l_Option_Alternative();
lean::mark_persistent(l_Option_Alternative);
return w;
}

// Lean compiler output
// Module: Init.Data.Option.Basic
// Imports: Init.Core Init.Control.Monad Init.Control.Alternative Init.Coe
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
lean_object* l_Option_getD___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Option_Monad___closed__10;
lean_object* l_Option_Alternative___lambda__1(lean_object*);
lean_object* l_Option_bind(lean_object*, lean_object*);
lean_object* l_Option_getD(lean_object*);
lean_object* l_Option_decidableRelLt(lean_object*, lean_object*);
lean_object* l_Option_DecidableEq(lean_object*);
lean_object* l_Option_decidableRelLt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_HasBeq(lean_object*);
lean_object* l_Option_HasBeq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_Alternative___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_isSome___rarg___boxed(lean_object*);
lean_object* l_Option_Monad___closed__6;
lean_object* l_Option_filter___rarg(lean_object*, lean_object*);
lean_object* l_Option_bind___rarg(lean_object*, lean_object*);
lean_object* l_Option_Monad___closed__3;
lean_object* l_Option_toBool(lean_object*);
lean_object* l_Option_Monad___closed__5;
lean_object* l_Option_Monad___closed__2;
uint8_t l_Option_isSome___rarg(lean_object*);
lean_object* l_Option_isSome(lean_object*);
lean_object* l_Option_Monad___closed__1;
lean_object* l_Option_Monad___closed__8;
lean_object* l_Option_Monad___closed__4;
lean_object* l_Option_Monad___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_isNone___rarg___boxed(lean_object*);
lean_object* l_Option_toMonad___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_Monad___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toMonad(lean_object*, lean_object*);
lean_object* l_Option_Monad___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_toMonad___boxed(lean_object*, lean_object*);
lean_object* l_Option_Monad;
lean_object* l_Option_HasLess___boxed(lean_object*, lean_object*);
lean_object* l_Option_HasLess(lean_object*, lean_object*);
lean_object* l_Option_Alternative___closed__2;
lean_object* l_Option_isNone(lean_object*);
lean_object* l_Option_orelse___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Option_Monad___lambda__2(lean_object*, lean_object*);
lean_object* l_Option_Alternative___closed__1;
lean_object* l_Option_map___rarg(lean_object*, lean_object*);
lean_object* l_Option_Monad___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_Alternative___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_map(lean_object*, lean_object*);
uint8_t l_Option_isNone___rarg(lean_object*);
uint8_t l_Option_toBool___rarg(lean_object*);
lean_object* l_Option_Monad___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_Alternative___closed__3;
lean_object* l_Option_Monad___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_DecidableEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_getD___rarg(lean_object*, lean_object*);
lean_object* l_Option_orelse(lean_object*);
lean_object* l_Option_Monad___closed__7;
lean_object* l_Option_Inhabited(lean_object*);
lean_object* l_Option_filter(lean_object*);
lean_object* l_Option_Monad___closed__9;
lean_object* l_Option_toBool___rarg___boxed(lean_object*);
lean_object* l_Option_Alternative;
lean_object* l_Option_orelse___rarg(lean_object*, lean_object*);
lean_object* l_Option_toMonad___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
}
}
lean_object* l_Option_toMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_toMonad___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Option_toMonad___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_toMonad(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Option_getD___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
lean_object* l_Option_getD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_getD___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Option_getD___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_getD___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Option_toBool___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Option_toBool(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_toBool___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Option_toBool___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Option_toBool___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Option_isSome___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Option_isSome(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_isSome___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Option_isSome___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Option_isSome___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Option_isNone___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Option_isNone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_isNone___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Option_isNone___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Option_isNone___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Option_bind___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
lean_object* l_Option_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_bind___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Option_map___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_Option_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_map___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Option_Monad___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
}
}
}
lean_object* l_Option_Monad___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Option_Monad___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_apply_1(x_7, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_1(x_7, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
}
lean_object* l_Option_Monad___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
}
lean_object* l_Option_Monad___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_inc(x_4);
return x_4;
}
}
}
lean_object* _init_l_Option_Monad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_map), 2, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Monad___lambda__1), 4, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Option_Monad___closed__1;
x_2 = l_Option_Monad___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Option_Monad___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Monad___lambda__2), 2, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Monad___lambda__3), 4, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Monad___lambda__4___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Monad___lambda__5___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Option_Monad___closed__3;
x_2 = l_Option_Monad___closed__4;
x_3 = l_Option_Monad___closed__5;
x_4 = l_Option_Monad___closed__6;
x_5 = l_Option_Monad___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Option_Monad___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_bind), 2, 0);
return x_1;
}
}
lean_object* _init_l_Option_Monad___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Option_Monad___closed__8;
x_2 = l_Option_Monad___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Option_Monad() {
_start:
{
lean_object* x_1; 
x_1 = l_Option_Monad___closed__10;
return x_1;
}
}
lean_object* l_Option_Monad___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Option_Monad___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Option_Monad___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Option_Monad___lambda__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Option_filter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
return x_2;
}
}
}
}
lean_object* l_Option_filter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_filter___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Option_orelse___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Option_orelse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_orelse___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Option_orelse___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_orelse___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Option_Alternative___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Option_Alternative___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
lean_object* _init_l_Option_Alternative___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Alternative___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_Option_Alternative___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_Alternative___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Option_Alternative___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Option_Monad;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Option_Alternative___closed__1;
x_4 = l_Option_Alternative___closed__2;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* _init_l_Option_Alternative() {
_start:
{
lean_object* x_1; 
x_1 = l_Option_Alternative___closed__3;
return x_1;
}
}
lean_object* l_Option_Alternative___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_Alternative___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Option_decidableRelLt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 1;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
lean_object* l_Option_decidableRelLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Option_decidableRelLt___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Option_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Option_DecidableEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
lean_object* l_Option_DecidableEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_DecidableEq___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Option_HasBeq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = lean_box(x_4);
return x_5;
}
else
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_2(x_1, x_10, x_11);
return x_12;
}
}
}
}
lean_object* l_Option_HasBeq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Option_HasBeq___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Option_HasLess(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_Option_HasLess___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_HasLess(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Control_Monad(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Option_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Monad(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Option_Monad___closed__1 = _init_l_Option_Monad___closed__1();
lean_mark_persistent(l_Option_Monad___closed__1);
l_Option_Monad___closed__2 = _init_l_Option_Monad___closed__2();
lean_mark_persistent(l_Option_Monad___closed__2);
l_Option_Monad___closed__3 = _init_l_Option_Monad___closed__3();
lean_mark_persistent(l_Option_Monad___closed__3);
l_Option_Monad___closed__4 = _init_l_Option_Monad___closed__4();
lean_mark_persistent(l_Option_Monad___closed__4);
l_Option_Monad___closed__5 = _init_l_Option_Monad___closed__5();
lean_mark_persistent(l_Option_Monad___closed__5);
l_Option_Monad___closed__6 = _init_l_Option_Monad___closed__6();
lean_mark_persistent(l_Option_Monad___closed__6);
l_Option_Monad___closed__7 = _init_l_Option_Monad___closed__7();
lean_mark_persistent(l_Option_Monad___closed__7);
l_Option_Monad___closed__8 = _init_l_Option_Monad___closed__8();
lean_mark_persistent(l_Option_Monad___closed__8);
l_Option_Monad___closed__9 = _init_l_Option_Monad___closed__9();
lean_mark_persistent(l_Option_Monad___closed__9);
l_Option_Monad___closed__10 = _init_l_Option_Monad___closed__10();
lean_mark_persistent(l_Option_Monad___closed__10);
l_Option_Monad = _init_l_Option_Monad();
lean_mark_persistent(l_Option_Monad);
l_Option_Alternative___closed__1 = _init_l_Option_Alternative___closed__1();
lean_mark_persistent(l_Option_Alternative___closed__1);
l_Option_Alternative___closed__2 = _init_l_Option_Alternative___closed__2();
lean_mark_persistent(l_Option_Alternative___closed__2);
l_Option_Alternative___closed__3 = _init_l_Option_Alternative___closed__3();
lean_mark_persistent(l_Option_Alternative___closed__3);
l_Option_Alternative = _init_l_Option_Alternative();
lean_mark_persistent(l_Option_Alternative);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

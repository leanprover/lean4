// Lean compiler output
// Module: Init.Data.Nat.Control
// Imports: Init.Control.Basic Init.Data.Nat.Basic Init.Omega
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
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop(lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM_loop(lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop(lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Nat_foldM_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM(lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM_loop(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Nat_forM(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___rarg(x_1, x_2, x_3, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_nat_sub(x_2, x_9);
x_12 = lean_nat_sub(x_11, x_8);
lean_dec(x_11);
lean_inc(x_3);
x_13 = lean_apply_2(x_3, x_12, lean_box(0));
x_14 = lean_alloc_closure((void*)(l_Nat_forM_loop___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forM_loop___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forM_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_forM_loop___rarg(x_1, x_2, x_3, x_2, lean_box(0));
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forRevM_loop___rarg(x_1, x_2, x_3, x_4, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_9);
x_11 = lean_apply_2(x_3, x_9, lean_box(0));
x_12 = lean_alloc_closure((void*)(l_Nat_forRevM_loop___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_9);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forRevM_loop___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forRevM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forRevM_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_forRevM_loop___rarg(x_1, x_2, x_3, x_2, lean_box(0));
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_forRevM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forRevM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_nat_sub(x_2, x_10);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
lean_inc(x_3);
x_14 = lean_apply_3(x_3, x_13, lean_box(0), x_6);
x_15 = lean_alloc_closure((void*)(l_Nat_foldM_loop___rarg___boxed), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_10);
lean_closure_set(x_15, 4, lean_box(0));
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldM_loop___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldM_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Nat_foldM_loop___rarg(x_1, x_2, x_3, x_2, lean_box(0), x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_10);
x_12 = lean_apply_3(x_3, x_10, lean_box(0), x_6);
x_13 = lean_alloc_closure((void*)(l_Nat_foldRevM_loop___rarg___boxed), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, lean_box(0));
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldRevM_loop___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldRevM_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Nat_foldRevM_loop___rarg(x_1, x_2, x_3, x_2, lean_box(0), x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldRevM___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Nat_allM_loop___rarg(x_1, x_2, x_3, x_4, lean_box(0));
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_nat_sub(x_2, x_9);
x_12 = lean_nat_sub(x_11, x_8);
lean_dec(x_11);
lean_inc(x_3);
x_13 = lean_apply_2(x_3, x_12, lean_box(0));
x_14 = lean_alloc_closure((void*)(l_Nat_allM_loop___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_apply_2(x_17, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Nat_allM_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_allM_loop___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Nat_allM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_allM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_allM_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_allM_loop___rarg(x_1, x_2, x_3, x_2, lean_box(0));
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_allM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_allM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Nat_anyM_loop___rarg(x_1, x_2, x_3, x_4, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_nat_sub(x_2, x_9);
x_12 = lean_nat_sub(x_11, x_8);
lean_dec(x_11);
lean_inc(x_3);
x_13 = lean_apply_2(x_3, x_12, lean_box(0));
x_14 = lean_alloc_closure((void*)(l_Nat_anyM_loop___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_apply_2(x_17, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Nat_anyM_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_anyM_loop___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Nat_anyM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_anyM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_anyM_loop___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_anyM_loop___rarg(x_1, x_2, x_3, x_2, lean_box(0));
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_anyM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_anyM___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Omega(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Control(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

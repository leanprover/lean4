// Lean compiler output
// Module: Init.Data.Nat.Control
// Imports: Init.Control.Monad Init.Control.Alternative Init.Data.Nat.Basic
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
lean_object* l_Nat_foldRevM___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyM___boxed(lean_object*);
lean_object* l_Nat_allMAux___main___boxed(lean_object*);
lean_object* l_Nat_forMAux___main(lean_object*);
lean_object* l_Nat_anyMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___main(lean_object*);
lean_object* l_Nat_foldRevM(lean_object*, lean_object*);
lean_object* l_Nat_foldM(lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___main(lean_object*);
lean_object* l_Nat_allMAux___boxed(lean_object*);
lean_object* l_Nat_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Nat_foldRevMAux___main(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux(lean_object*, lean_object*);
lean_object* l_Nat_forRevM___boxed(lean_object*);
lean_object* l_Nat_allMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allMAux___main(lean_object*);
lean_object* l_Nat_forRevM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Nat_foldRevMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___boxed(lean_object*);
lean_object* l_Nat_forRevM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allM(lean_object*);
lean_object* l_Nat_foldRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM___boxed(lean_object*, lean_object*);
lean_object* l_Nat_anyMAux(lean_object*);
lean_object* l_Nat_allMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyM(lean_object*);
lean_object* l_Nat_forRevMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___boxed(lean_object*);
lean_object* l_Nat_forRevMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux(lean_object*);
lean_object* l_Nat_forM(lean_object*);
lean_object* l_Nat_allMAux(lean_object*);
lean_object* l_Nat_anyMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allM___boxed(lean_object*);
lean_object* l_Nat_forRevM(lean_object*);
lean_object* l_Nat_foldRevM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyMAux___main___boxed(lean_object*);
lean_object* l_Nat_foldMAux___main(lean_object*, lean_object*);
lean_object* l_Nat_forRevMAux___main___boxed(lean_object*);
lean_object* l_Nat_forMAux___main___boxed(lean_object*);
lean_object* l_Nat_foldMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Nat_allM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_allMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_nat_sub(x_3, x_8);
x_11 = lean_nat_sub(x_10, x_7);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_alloc_closure((void*)(l_Nat_forMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_8);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
return x_18;
}
}
}
lean_object* l_Nat_forMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forMAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_forMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_forMAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_forMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_forMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_forMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_forMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forMAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_forMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_forMAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_forMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_forMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_forMAux___main___rarg(x_1, x_3, x_2, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_forM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_forM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_forRevMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_forRevMAux___main___rarg(x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Nat_forRevMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_7);
x_9 = lean_apply_1(x_2, x_7);
x_10 = lean_alloc_closure((void*)(l_Nat_forRevMAux___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
lean_object* l_Nat_forRevMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forRevMAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_forRevMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_forRevMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_forRevMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_forRevMAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_forRevMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_forRevMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_forRevMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_forRevMAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_forRevMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forRevMAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_forRevMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_forRevMAux___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_forRevMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_forRevMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_forRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_forRevMAux___main___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Nat_forRevM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_forRevM___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_forRevM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_forRevM___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_forRevM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_forRevM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_nat_sub(x_3, x_9);
x_12 = lean_nat_sub(x_11, x_8);
lean_dec(x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_2, x_12, x_5);
x_14 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___rarg___boxed), 5, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_9);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_5);
return x_18;
}
}
}
lean_object* l_Nat_foldMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldMAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_foldMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldMAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Nat_foldMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldMAux___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Nat_foldMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldMAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Nat_foldMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_foldMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
x_5 = l_Nat_foldMAux___main___rarg(x_1, x_2, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_foldM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Nat_foldM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_foldM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldRevMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_8);
x_10 = lean_apply_2(x_2, x_8, x_4);
x_11 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___rarg___boxed), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_8);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_4);
return x_15;
}
}
}
lean_object* l_Nat_foldRevMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Nat_foldRevMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevMAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_foldRevMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_foldRevMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldRevMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_foldRevMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Nat_foldRevMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevMAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_foldRevMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_foldRevMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_foldRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevMAux___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Nat_foldRevM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_foldRevM___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Nat_foldRevM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldRevM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_foldRevM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_foldRevM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_allMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(x_5);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Nat_allMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_10;
}
}
}
lean_object* l_Nat_allMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_nat_sub(x_3, x_8);
x_11 = lean_nat_sub(x_10, x_7);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_alloc_closure((void*)(l_Nat_allMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_8);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_apply_2(x_16, lean_box(0), x_18);
return x_19;
}
}
}
lean_object* l_Nat_allMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_allMAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_allMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Nat_allMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Nat_allMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_allMAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_allMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_allMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_allMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_allMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_allMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_allMAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_allMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_allMAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_allMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_allMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_allMAux___main___rarg(x_1, x_3, x_2, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_allM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_allM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_allM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_allM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_anyMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Nat_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(x_5);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
lean_object* l_Nat_anyMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_nat_sub(x_3, x_8);
x_11 = lean_nat_sub(x_10, x_7);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_alloc_closure((void*)(l_Nat_anyMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_8);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_apply_2(x_16, lean_box(0), x_18);
return x_19;
}
}
}
lean_object* l_Nat_anyMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_anyMAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_anyMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Nat_anyMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Nat_anyMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_anyMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_anyMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_anyMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_anyMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_anyMAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_anyMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_anyMAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_anyMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_anyMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_anyMAux___main___rarg(x_1, x_3, x_2, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_anyM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_anyM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_anyM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_anyM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Control_Monad(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Nat_Control(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Monad(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

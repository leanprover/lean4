// Lean compiler output
// Module: init.data.nat.basic
// Imports: init.core
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
lean_object* l_Nat_decLe___boxed(lean_object*, lean_object*);
uint8_t l_Prod_allI(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Prod_foldI(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at_Nat_all___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repeatAux(lean_object*);
lean_object* l_Nat_HasPow;
lean_object* l_Prod_foldI___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_fold___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_fold(lean_object*);
lean_object* l_Nat_anyAux___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Prod_anyI(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_allI___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repeatAux___main(lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
uint8_t l_Nat_all(lean_object*, lean_object*);
uint8_t l_Nat_any(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_any___boxed(lean_object*, lean_object*);
lean_object* l_Nat_pred(lean_object*);
lean_object* l_Nat_sub___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Nat_all___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_ble___boxed(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at_Prod_allI___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_HasSub___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_HasPow___closed__1;
lean_object* l_Nat_repeat___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux(lean_object*);
lean_object* l_Prod_anyI___boxed(lean_object*, lean_object*);
lean_object* l_Nat_pow___main(lean_object*, lean_object*);
lean_object* l_Nat_HasSub;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Nat_pow___main___boxed(lean_object*, lean_object*);
lean_object* l_Nat_beq___boxed(lean_object*, lean_object*);
lean_object* l_Nat_pow(lean_object*, lean_object*);
lean_object* l_Prod_foldI___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main(lean_object*);
uint8_t l_Nat_anyAux___main___at_Nat_all___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_pred___boxed(lean_object*);
lean_object* l_Nat_HasLessEq;
lean_object* l_Nat_pow___boxed(lean_object*, lean_object*);
lean_object* l_Nat_HasLess;
lean_object* l_Nat_foldAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_HasMul;
lean_object* l_Nat_repeatAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at_Prod_allI___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repeatAux___main___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repeat(lean_object*);
lean_object* l_Nat_DecidableEq___closed__1;
lean_object* l_Nat_max___boxed(lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Nat_DecidableEq;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_HasMul___closed__1;
lean_object* l_Nat_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_nat_dec_eq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_nat_dec_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Nat_DecidableEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Nat_DecidableEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_DecidableEq___closed__1;
return x_1;
}
}
lean_object* l_Nat_ble___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_nat_dec_le(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Nat_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Nat_HasLess() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Nat_pred___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_sub(x_1, lean_box(1));
return x_2;
}
}
lean_object* l_Nat_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_sub(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Nat_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Nat_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_Nat_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Nat_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasMul___closed__1;
return x_1;
}
}
lean_object* l_Nat_foldAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
x_9 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_4);
x_3 = x_8;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_Nat_foldAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_foldAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_foldAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Nat_foldAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_foldAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_foldAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_foldAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Nat_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Nat_foldAux___main___rarg(x_1, x_2, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_fold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_fold___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Nat_anyAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
lean_object* l_Nat_anyAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___main(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Nat_anyAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Nat_anyAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_anyAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Nat_any(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
x_3 = l_Nat_anyAux___main(x_1, x_2, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_any(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Nat_anyAux___main___at_Nat_all___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
else
{
x_3 = x_7;
goto _start;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8_t l_Nat_all(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
x_3 = l_Nat_anyAux___main___at_Nat_all___spec__1(x_1, x_2, x_2);
lean_dec(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Nat_anyAux___main___at_Nat_all___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___main___at_Nat_all___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Nat_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_all(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_repeatAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Nat_repeatAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_repeatAux___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_repeatAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_repeatAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_repeatAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_repeatAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_repeat___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_repeatAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_repeat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_repeat___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_pow___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Nat_pow___main(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_mul(x_7, x_1);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
lean_object* l_Nat_pow___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_pow___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_pow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_pow___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Nat_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_pow(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Nat_HasPow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_pow___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Nat_HasPow() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_HasPow___closed__1;
return x_1;
}
}
lean_object* l_Nat_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_nat_dec_le(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_nat_dec_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_max(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_Nat_max___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_max(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Prod_foldI___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_sub(x_4, x_5);
x_7 = l_Nat_foldAux___main___rarg(x_1, x_4, x_6, x_3);
return x_7;
}
}
lean_object* l_Prod_foldI(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Prod_foldI___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Prod_foldI___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Prod_foldI___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Prod_anyI(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_sub(x_3, x_4);
x_6 = l_Nat_anyAux___main(x_1, x_3, x_5);
return x_6;
}
}
lean_object* l_Prod_anyI___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Prod_anyI(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Nat_anyAux___main___at_Prod_allI___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
else
{
x_3 = x_7;
goto _start;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8_t l_Prod_allI(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_sub(x_3, x_4);
x_6 = l_Nat_anyAux___main___at_Prod_allI___spec__1(x_1, x_3, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
lean_object* l_Nat_anyAux___main___at_Prod_allI___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Nat_anyAux___main___at_Prod_allI___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Prod_allI___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Prod_allI(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_init_core(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_nat_basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (lean_io_result_is_error(w)) return w;
l_Nat_DecidableEq___closed__1 = _init_l_Nat_DecidableEq___closed__1();
lean_mark_persistent(l_Nat_DecidableEq___closed__1);
l_Nat_DecidableEq = _init_l_Nat_DecidableEq();
lean_mark_persistent(l_Nat_DecidableEq);
l_Nat_HasLessEq = _init_l_Nat_HasLessEq();
lean_mark_persistent(l_Nat_HasLessEq);
l_Nat_HasLess = _init_l_Nat_HasLess();
lean_mark_persistent(l_Nat_HasLess);
l_Nat_HasSub___closed__1 = _init_l_Nat_HasSub___closed__1();
lean_mark_persistent(l_Nat_HasSub___closed__1);
l_Nat_HasSub = _init_l_Nat_HasSub();
lean_mark_persistent(l_Nat_HasSub);
l_Nat_HasMul___closed__1 = _init_l_Nat_HasMul___closed__1();
lean_mark_persistent(l_Nat_HasMul___closed__1);
l_Nat_HasMul = _init_l_Nat_HasMul();
lean_mark_persistent(l_Nat_HasMul);
l_Nat_HasPow___closed__1 = _init_l_Nat_HasPow___closed__1();
lean_mark_persistent(l_Nat_HasPow___closed__1);
l_Nat_HasPow = _init_l_Nat_HasPow();
lean_mark_persistent(l_Nat_HasPow);
return w;
}
#ifdef __cplusplus
}
#endif

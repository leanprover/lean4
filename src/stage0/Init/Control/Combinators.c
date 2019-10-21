// Lean compiler output
// Module: Init.Control.Combinators
// Imports: Init.Control.Monad Init.Control.Alternative Init.Data.List.Basic
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
lean_object* l_List_mfoldl___main(lean_object*);
lean_object* l_Nat_mforRevAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main(lean_object*);
lean_object* l_List_mmap(lean_object*);
lean_object* l_Nat_mforAux___boxed(lean_object*);
lean_object* l_List_mfor_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mforall___main(lean_object*);
lean_object* l_mcond___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_mexists___main(lean_object*);
lean_object* l_List_mmap_u2082___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unless___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfilter___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfoldr___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux___main___boxed(lean_object*);
lean_object* l_List_mexists___boxed(lean_object*);
lean_object* l_Nat_mforAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mcond___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mjoin___rarg___closed__1;
lean_object* l_Nat_mforRev___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mcond___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_List_mmap_u2082(lean_object*);
lean_object* l_Nat_mfold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfilter___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mjoin___boxed(lean_object*);
lean_object* l_Nat_mforAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfilter___main___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mmap___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfirst___main___boxed(lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_when___boxed(lean_object*);
lean_object* l_List_mmap___main___boxed(lean_object*);
lean_object* l_List_mmap___boxed(lean_object*);
lean_object* l_List_mfor_u2082___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___boxed(lean_object*);
lean_object* l_Nat_mforRev(lean_object*);
lean_object* l_Nat_mfoldRevAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforRevAux___boxed(lean_object*);
lean_object* l_Nat_mfoldAux___main(lean_object*, lean_object*);
lean_object* l_Nat_mfoldRevAux(lean_object*, lean_object*);
lean_object* l_List_mfirst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfoldr(lean_object*);
lean_object* l_List_mfor_u2082___main___boxed(lean_object*);
lean_object* l_Nat_mfoldRevAux___main(lean_object*, lean_object*);
lean_object* l_Nat_mforRevAux___main(lean_object*);
lean_object* l_Nat_mfoldRevAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfilter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mcond___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_when___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_List_mfoldr___boxed(lean_object*);
lean_object* l_List_mforall___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___main___boxed(lean_object*, lean_object*);
lean_object* l_List_mmap___main___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_List_mfoldl___main___boxed(lean_object*);
lean_object* l_mwhen___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_List_mfoldr___main(lean_object*);
lean_object* l_Nat_mforRev___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfoldl___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor_u2082(lean_object*);
lean_object* l_List_mfirst___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mforall___main___boxed(lean_object*);
lean_object* l_Nat_mfoldRevAux___main___boxed(lean_object*, lean_object*);
lean_object* l_List_mmap_u2082___boxed(lean_object*);
lean_object* l_List_mmap_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mforall___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unless___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_List_mfoldr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfor(lean_object*);
lean_object* l_Nat_mfoldRevAux___boxed(lean_object*, lean_object*);
lean_object* l_List_mmap___main(lean_object*);
lean_object* l_List_mexists___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor_u2082___main(lean_object*);
lean_object* l_List_mfilter___boxed(lean_object*);
lean_object* l_List_mmap___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_when___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfoldl___boxed(lean_object*);
lean_object* l_List_mfoldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mjoin___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor_u2082___boxed(lean_object*);
lean_object* l_Nat_mfoldRevAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfilter___main___boxed(lean_object*);
lean_object* l_mjoin(lean_object*);
lean_object* l_List_mfor___main(lean_object*);
lean_object* l_Nat_mforAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforRevAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_mwhen___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mforall(lean_object*);
lean_object* l_Nat_mforRevAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforRevAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfor___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfold___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mfoldRev___boxed(lean_object*, lean_object*);
lean_object* l_List_mforall___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Nat_mfoldRevAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfold(lean_object*, lean_object*);
lean_object* l_Nat_mforAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mfilter(lean_object*);
lean_object* l_mwhen___boxed(lean_object*);
lean_object* l_List_mfor___boxed(lean_object*);
lean_object* l_List_mmap_u2082___main(lean_object*);
lean_object* l_List_mfoldl___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforAux(lean_object*);
lean_object* l_Nat_mfoldAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unless___boxed(lean_object*);
lean_object* l_List_mfirst(lean_object*, lean_object*);
lean_object* l_List_mmap_u2082___main___boxed(lean_object*);
lean_object* l_List_mfoldr___main___boxed(lean_object*);
lean_object* l_Nat_mforRev___boxed(lean_object*);
lean_object* l_List_mfilter___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldRev(lean_object*, lean_object*);
lean_object* l_List_mfilter___main(lean_object*);
lean_object* l_List_mexists___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldRev___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mforall___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mmap___main___rarg___closed__1;
lean_object* l_Nat_mforRevAux___main___boxed(lean_object*);
lean_object* l_List_mforall___boxed(lean_object*);
lean_object* l_List_mfoldl(lean_object*);
lean_object* l_List_mfor(lean_object*);
lean_object* l_Nat_mfor___boxed(lean_object*);
lean_object* l_List_mfirst___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mfor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_mcond(lean_object*);
lean_object* l_List_mfilter___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Nat_mfor___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___boxed(lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux(lean_object*, lean_object*);
lean_object* l_unless(lean_object*);
lean_object* l_when(lean_object*);
lean_object* l_List_mexists___main___boxed(lean_object*);
lean_object* l_List_mexists(lean_object*);
lean_object* l_List_mfor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mforRevAux(lean_object*);
lean_object* l_mwhen___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldRev___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mexists___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mwhen(lean_object*);
lean_object* l_List_mfirst___main(lean_object*);
lean_object* l_List_mexists___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* _init_l_mjoin___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_mjoin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_mjoin___rarg___closed__1;
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
lean_object* l_mjoin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_mjoin___rarg), 3, 0);
return x_2;
}
}
lean_object* l_mjoin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mjoin(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_when___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
}
}
lean_object* l_when(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_when___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_when___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_when___rarg(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_when___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_when(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_unless___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
}
lean_object* l_unless(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unless___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_unless___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_unless___rarg(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_unless___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_unless(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_mcond___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
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
lean_object* l_mcond___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_mcond___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_3, x_7);
return x_8;
}
}
lean_object* l_mcond(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_mcond___rarg), 5, 0);
return x_2;
}
}
lean_object* l_mcond___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_mcond___rarg___lambda__1(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_mcond___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mcond(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_mwhen___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_mwhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_mwhen___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
lean_object* l_mwhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_mwhen___rarg), 3, 0);
return x_2;
}
}
lean_object* l_mwhen___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_mwhen___rarg___lambda__1(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_mwhen___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mwhen(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mforAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_nat_sub(x_3, x_8);
x_11 = lean_nat_sub(x_10, x_7);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = l_Nat_mforAux___main___rarg(x_1, x_2, x_3, x_8);
lean_dec(x_8);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
}
}
lean_object* l_Nat_mforAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_mforAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_mforAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mforAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_mforAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_mforAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mforAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mforAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_mforAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_mforAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Nat_mforAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mforAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_mforAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_mforAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mfor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mforAux___main___rarg(x_1, x_3, x_2, x_2);
return x_4;
}
}
lean_object* l_Nat_mfor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_mfor___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_mfor___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mfor___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_mfor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_mfor(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mforRevAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_7);
x_9 = lean_apply_1(x_2, x_7);
x_10 = l_Nat_mforRevAux___main___rarg(x_1, x_2, x_7);
lean_dec(x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
lean_object* l_Nat_mforRevAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_mforRevAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_mforRevAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mforRevAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_mforRevAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_mforRevAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mforRevAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mforRevAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Nat_mforRevAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_mforRevAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_mforRevAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mforRevAux___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_mforRevAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_mforRevAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mforRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mforRevAux___main___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Nat_mforRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_mforRev___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Nat_mforRev___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_mforRev___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_mforRev___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_mforRev(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_mfoldAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_14 = lean_alloc_closure((void*)(l_Nat_mfoldAux___main___rarg___boxed), 5, 4);
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
lean_object* l_Nat_mfoldAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_mfoldAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Nat_mfoldAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mfoldAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Nat_mfoldAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_mfoldAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_mfoldAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mfoldAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Nat_mfoldAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_mfoldAux___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Nat_mfoldAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_mfoldAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Nat_mfoldAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_mfoldAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_mfold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
x_5 = l_Nat_mfoldAux___main___rarg(x_1, x_2, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_mfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_mfold___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Nat_mfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_mfold(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_mfoldRevAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = lean_alloc_closure((void*)(l_Nat_mfoldRevAux___main___rarg___boxed), 4, 3);
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
lean_object* l_Nat_mfoldRevAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_mfoldRevAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Nat_mfoldRevAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mfoldRevAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_mfoldRevAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_mfoldRevAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_mfoldRevAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mfoldRevAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_mfoldRevAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_mfoldRevAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Nat_mfoldRevAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mfoldRevAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Nat_mfoldRevAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_mfoldRevAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Nat_mfoldRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mfoldRevAux___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Nat_mfoldRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Nat_mfoldRev___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Nat_mfoldRev___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_mfoldRev___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_mfoldRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_mfoldRev(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_List_mmap___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_List_mmap___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_mmap___main___rarg___lambda__1), 2, 0);
return x_1;
}
}
lean_object* l_List_mmap___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
x_14 = lean_apply_1(x_4, x_9);
x_15 = l_List_mmap___main___rarg___closed__1;
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_14);
x_17 = l_List_mmap___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_10);
x_18 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
}
lean_object* l_List_mmap___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mmap___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mmap___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mmap___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mmap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mmap___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_mmap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mmap___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mmap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mmap(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mmap_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
x_13 = lean_box(0);
x_8 = x_13;
goto block_12;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_box(0);
x_8 = x_14;
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_5);
x_22 = lean_apply_2(x_5, x_15, x_17);
x_23 = l_List_mmap___main___rarg___closed__1;
x_24 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_23, x_22);
x_25 = l_List_mmap_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_16, x_18);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l_List_mmap_u2082___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mmap_u2082___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mmap_u2082___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mmap_u2082___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mmap_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mmap_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_mmap_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mmap_u2082___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mmap_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mmap_u2082(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfor___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_4);
x_12 = lean_apply_1(x_4, x_9);
x_13 = l_List_mfor___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_10);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
lean_object* l_List_mfor___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfor___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mfor___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfor___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mfor___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_mfor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfor___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mfor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfor(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfor_u2082___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_inc(x_5);
x_19 = lean_apply_2(x_5, x_14, x_16);
x_20 = l_List_mfor_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_15, x_17);
x_21 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
}
}
lean_object* l_List_mfor_u2082___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfor_u2082___main___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mfor_u2082___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfor_u2082___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfor_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mfor_u2082___main___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_mfor_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfor_u2082___rarg), 7, 0);
return x_2;
}
}
lean_object* l_List_mfor_u2082___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfor_u2082(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfilter___main___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l_List_mfilter___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = l_List_mfilter___main___rarg(x_1, lean_box(0), x_2, x_3);
x_8 = lean_box(x_6);
x_9 = lean_alloc_closure((void*)(l_List_mfilter___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_List_mfilter___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_8);
x_11 = lean_apply_1(x_3, x_8);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_List_mfilter___main___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_8);
lean_closure_set(x_12, 4, x_10);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_List_mfilter___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfilter___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mfilter___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_List_mfilter___main___rarg___lambda__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_List_mfilter___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_List_mfilter___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* l_List_mfilter___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfilter___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfilter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mfilter___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_List_mfilter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfilter___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mfilter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfilter(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfoldl___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mfoldl___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_List_mfoldl___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_4);
x_13 = lean_apply_2(x_4, x_5, x_10);
x_14 = lean_alloc_closure((void*)(l_List_mfoldl___main___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_mfoldl___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfoldl___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_mfoldl___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfoldl___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfoldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mfoldl___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_List_mfoldl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfoldl___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_mfoldl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfoldl(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfoldr___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_4);
x_13 = l_List_mfoldr___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_11);
x_14 = lean_apply_1(x_4, x_10);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_mfoldr___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfoldr___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_mfoldr___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfoldr___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfoldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mfoldr___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_List_mfoldr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfoldr___rarg), 6, 0);
return x_2;
}
}
lean_object* l_List_mfoldr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfoldr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfirst___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_inc(x_4);
x_11 = lean_apply_1(x_4, x_8);
x_12 = l_List_mfirst___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_9);
x_13 = lean_apply_3(x_10, lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_List_mfirst___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mfirst___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mfirst___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mfirst___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mfirst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mfirst___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_List_mfirst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_mfirst___rarg), 5, 0);
return x_3;
}
}
lean_object* l_List_mfirst___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_mfirst(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_mexists___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_List_mexists___main___rarg(x_1, lean_box(0), x_2, x_3);
return x_5;
}
else
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
x_8 = lean_box(x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
}
lean_object* l_List_mexists___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_apply_1(x_3, x_10);
x_14 = lean_alloc_closure((void*)(l_List_mexists___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_mexists___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mexists___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mexists___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_List_mexists___main___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_List_mexists___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mexists___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mexists___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mexists___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_List_mexists(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mexists___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mexists___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mexists(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mforall___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_List_mforall___main___rarg(x_1, lean_box(0), x_2, x_3);
return x_9;
}
}
}
lean_object* l_List_mforall___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_apply_1(x_3, x_10);
x_14 = lean_alloc_closure((void*)(l_List_mforall___main___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_List_mforall___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mforall___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mforall___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_List_mforall___main___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_List_mforall___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mforall___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mforall___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mforall___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_List_mforall(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mforall___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_mforall___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_mforall(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Control_Monad(lean_object*);
lean_object* initialize_Init_Control_Alternative(lean_object*);
lean_object* initialize_Init_Data_List_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Control_Combinators(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Monad(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Alternative(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_mjoin___rarg___closed__1 = _init_l_mjoin___rarg___closed__1();
lean_mark_persistent(l_mjoin___rarg___closed__1);
l_List_mmap___main___rarg___closed__1 = _init_l_List_mmap___main___rarg___closed__1();
lean_mark_persistent(l_List_mmap___main___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

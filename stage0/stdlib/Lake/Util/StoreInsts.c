// Lean compiler output
// Module: Lake.Util.StoreInsts
// Imports: Init Lake.Util.DRBMap Lake.Util.RBArray Lake.Util.Family Lake.Util.Store
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
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lake_RBNode_dFind___rarg(x_1, lean_box(0), x_6, x_2);
lean_ctor_set(x_4, 0, x_7);
x_8 = lean_apply_2(x_3, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Lake_RBNode_dFind___rarg(x_1, lean_box(0), x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_apply_2(x_3, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_RBNode_insert___rarg(x_2, x_5, x_3, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__2), 4, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__3), 5, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_6, x_2);
lean_ctor_set(x_4, 0, x_7);
x_8 = lean_apply_2(x_3, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_apply_2(x_3, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBMapOfMonad___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBMapOfMonad___rarg___lambda__2), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadDStoreStateTDRBMapOfMonadOfEqOfCmpWrt___rarg___lambda__3), 5, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBMapOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBMapOfMonad___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_7, x_2);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_apply_2(x_3, lean_box(0), x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_RBNode_find___rarg(x_1, lean_box(0), x_12, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_apply_2(x_3, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lake_RBArray_insert___rarg(x_2, x_5, x_3, x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__2), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg___lambda__3), 5, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreStateTRBArrayOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadStoreStateTRBArrayOfMonad___rarg), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_5, x_1);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_apply_2(x_2, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_8, x_1);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_6);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_2, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_apply_2(x_6, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__2), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__3), 4, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instMonadStoreNameStateTNameMapOfMonad___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_apply_1(x_5, x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadStore1OfOfMonadDStoreOfFamilyOut___rarg), 4, 0);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_DRBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_RBArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Family(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Store(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_DRBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_RBArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Family(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Store(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

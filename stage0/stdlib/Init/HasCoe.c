// Lean compiler output
// Module: Init.HasCoe
// Imports: Init.Data.List.Basic
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
lean_object* l_Legacy_coeSubtype(lean_object*, lean_object*);
lean_object* l_Legacy_liftPair_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeoeTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_oldCoeSort___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_liftFnRange___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeSubtype___rarg(lean_object*);
lean_object* l_Legacy_liftTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeToLift(lean_object*, lean_object*);
lean_object* l_oldCoeT___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_liftFnDom(lean_object*, lean_object*, lean_object*);
lean_object* l_lift(lean_object*, lean_object*);
lean_object* l_oldCoeFnB___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_coeBase___rarg(lean_object*);
lean_object* l_Legacy_coeBaseAux___rarg(lean_object*);
uint8_t l_Legacy_coeDecidableEq(uint8_t);
lean_object* l_oldCoeFn(lean_object*);
lean_object* l_Legacy_oldCoeOption___rarg(lean_object*);
lean_object* l_oldCoe(lean_object*, lean_object*);
lean_object* l_oldCoeFn___rarg(lean_object*, lean_object*);
extern lean_object* l_Nat_HasOfNat___closed__1;
lean_object* l_Legacy_liftFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_oldCoe___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_coeBase(lean_object*, lean_object*);
lean_object* l_oldCoeToLift(lean_object*, lean_object*);
lean_object* l_Legacy_liftRefl(lean_object*);
lean_object* l_Legacy_coeBaseAux(lean_object*, lean_object*);
lean_object* l_Legacy_liftList___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_coeSortTrans(lean_object*, lean_object*);
lean_object* l_liftT(lean_object*, lean_object*);
lean_object* l_Legacy_coeBoolToProp;
lean_object* l_Legacy_liftList(lean_object*, lean_object*);
lean_object* l_oldCoeB___rarg(lean_object*, lean_object*);
lean_object* l_oldCoeSort(lean_object*);
lean_object* l_Legacy_liftPair_u2081(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeFnTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeSortBool;
lean_object* l_Legacy_liftFnDom___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeSubtype___boxed(lean_object*, lean_object*);
lean_object* l_Legacy_coeTransAux(lean_object*, lean_object*, lean_object*);
lean_object* l_oldCoeFnB(lean_object*);
lean_object* l_Legacy_coeoeTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeTransAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_liftPair_u2081___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_liftFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeSubtype___rarg___boxed(lean_object*);
lean_object* l_Legacy_coeSortTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_liftPair(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_oldCoeOption(lean_object*);
lean_object* l_Legacy_coeToLift___rarg(lean_object*);
lean_object* l_oldCoeToLift___rarg(lean_object*);
lean_object* l_Legacy_coeFnTrans(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Legacy_liftList___spec__1(lean_object*, lean_object*);
lean_object* l_oldCoeT(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Legacy_liftList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_oldCoeB(lean_object*, lean_object*);
lean_object* l_lift___rarg(lean_object*, lean_object*);
lean_object* l_Legacy_liftTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_liftPair___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_liftFnRange(lean_object*, lean_object*, lean_object*);
lean_object* l_Legacy_coeDecidableEq___boxed(lean_object*);
lean_object* l_Legacy_liftPair_u2082___rarg(lean_object*, lean_object*);
lean_object* l_liftT___rarg(lean_object*, lean_object*);
lean_object* l_lift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_lift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_lift___rarg), 2, 0);
return x_3;
}
}
lean_object* l_liftT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_liftT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_liftT___rarg), 2, 0);
return x_3;
}
}
lean_object* l_oldCoeB___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_oldCoeB(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_oldCoeB___rarg), 2, 0);
return x_3;
}
}
lean_object* l_oldCoeT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_oldCoeT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_oldCoeT___rarg), 2, 0);
return x_3;
}
}
lean_object* l_oldCoeFnB___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_oldCoeFnB(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeFnB___rarg), 2, 0);
return x_2;
}
}
lean_object* l_oldCoe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_oldCoe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_oldCoe___rarg), 2, 0);
return x_3;
}
}
lean_object* l_oldCoeFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_oldCoeFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeFn___rarg), 2, 0);
return x_2;
}
}
lean_object* l_oldCoeSort___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_oldCoeSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeSort___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Legacy_liftTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Legacy_liftTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_liftTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Legacy_liftRefl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_HasOfNat___closed__1;
return x_2;
}
}
lean_object* l_Legacy_coeoeTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Legacy_coeoeTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_coeoeTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Legacy_coeBase___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeB___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Legacy_coeBase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_coeBase___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Legacy_oldCoeOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Legacy_oldCoeOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Legacy_oldCoeOption___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Legacy_coeTransAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Legacy_coeTransAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_coeTransAux___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Legacy_coeBaseAux___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeB___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Legacy_coeBaseAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_coeBaseAux___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Legacy_coeFnTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Legacy_coeFnTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_coeFnTrans___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Legacy_coeSortTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Legacy_coeSortTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_coeSortTrans___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Legacy_coeToLift___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeT___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Legacy_coeToLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_coeToLift___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_Legacy_coeBoolToProp() {
_start:
{
return lean_box(0);
}
}
lean_object* _init_l_Legacy_coeSortBool() {
_start:
{
return lean_box(0);
}
}
uint8_t l_Legacy_coeDecidableEq(uint8_t x_1) {
_start:
{
if (x_1 == 0)
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
lean_object* l_Legacy_coeDecidableEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Legacy_coeDecidableEq(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Legacy_coeSubtype___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Legacy_coeSubtype(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_coeSubtype___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Legacy_coeSubtype___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Legacy_coeSubtype___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Legacy_coeSubtype___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Legacy_coeSubtype(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Legacy_liftFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_apply_1(x_1, x_6);
return x_7;
}
}
lean_object* l_Legacy_liftFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Legacy_liftFn___rarg), 4, 0);
return x_5;
}
}
lean_object* l_Legacy_liftFnRange___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Legacy_liftFnRange(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_liftFnRange___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Legacy_liftFnDom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_Legacy_liftFnDom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_liftFnDom___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Legacy_liftPair___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_apply_1(x_2, x_6);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_apply_1(x_1, x_9);
x_12 = lean_apply_1(x_2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Legacy_liftPair(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Legacy_liftPair___rarg), 3, 0);
return x_5;
}
}
lean_object* l_Legacy_liftPair_u2081___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Legacy_liftPair_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_liftPair_u2081___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Legacy_liftPair_u2082___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Legacy_liftPair_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Legacy_liftPair_u2082___rarg), 2, 0);
return x_4;
}
}
lean_object* l_List_map___main___at_Legacy_liftList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_List_map___main___at_Legacy_liftList___spec__1___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_List_map___main___at_Legacy_liftList___spec__1___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_Legacy_liftList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_Legacy_liftList___spec__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Legacy_liftList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Legacy_liftList___spec__1___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Legacy_liftList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Legacy_liftList___rarg), 2, 0);
return x_3;
}
}
lean_object* l_oldCoeToLift___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_oldCoeT___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_oldCoeToLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_oldCoeToLift___rarg), 1, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_List_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_HasCoe(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Legacy_coeBoolToProp = _init_l_Legacy_coeBoolToProp();
l_Legacy_coeSortBool = _init_l_Legacy_coeSortBool();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

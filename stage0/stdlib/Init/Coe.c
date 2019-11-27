// Lean compiler output
// Module: Init.Coe
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
lean_object* l_coeOption___rarg(lean_object*);
lean_object* l_coeBase___rarg(lean_object*);
lean_object* l_coeSubtype(lean_object*, lean_object*);
lean_object* l_liftPair_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_coeToLift___rarg(lean_object*);
lean_object* l_liftFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_liftList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_liftPair(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_coeSubtype___rarg(lean_object*);
lean_object* l_coeBoolToProp;
lean_object* l_coeBase(lean_object*, lean_object*);
lean_object* l_coeTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_coeB___rarg(lean_object*, lean_object*);
lean_object* l_coeT(lean_object*, lean_object*);
lean_object* l_coeFnTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_liftList(lean_object*, lean_object*);
lean_object* l_lift(lean_object*, lean_object*);
lean_object* l_liftRefl(lean_object*);
lean_object* l_liftPair_u2081(lean_object*, lean_object*, lean_object*);
lean_object* l_coeSortTrans(lean_object*, lean_object*);
lean_object* l_liftPair_u2082___rarg(lean_object*, lean_object*);
lean_object* l_coeSort___rarg(lean_object*, lean_object*);
lean_object* l_liftPair___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeBaseAux(lean_object*, lean_object*);
lean_object* l_coeFn(lean_object*);
lean_object* l_List_map___main___at_liftList___spec__1(lean_object*, lean_object*);
lean_object* l_liftT(lean_object*, lean_object*);
lean_object* l_coeOption(lean_object*);
lean_object* l_liftTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeSubtype___boxed(lean_object*, lean_object*);
lean_object* l_liftFnRange(lean_object*, lean_object*, lean_object*);
lean_object* l_liftTrans(lean_object*, lean_object*, lean_object*);
lean_object* l_coeTransAux(lean_object*, lean_object*, lean_object*);
lean_object* l_liftFnDom___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeFnB___rarg(lean_object*, lean_object*);
lean_object* l_coeFn___rarg(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_coeSubtype___rarg___boxed(lean_object*);
lean_object* l_coe___rarg(lean_object*, lean_object*);
lean_object* l_liftFnDom(lean_object*, lean_object*, lean_object*);
lean_object* l_coeTransAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coe(lean_object*, lean_object*);
lean_object* l_coeSortTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeDecidableEq___boxed(lean_object*);
lean_object* l_coeFnTrans(lean_object*, lean_object*);
lean_object* l_liftPair_u2081___rarg(lean_object*, lean_object*);
lean_object* l_coeTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_coeFnB(lean_object*);
lean_object* l_liftRefl___closed__1;
lean_object* l_coeB(lean_object*, lean_object*);
lean_object* l_liftFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_coeT___rarg(lean_object*, lean_object*);
lean_object* l_coeSort(lean_object*);
lean_object* l_coeSortBool;
lean_object* l_coeToLift(lean_object*, lean_object*);
lean_object* l_liftFnRange___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_lift___rarg(lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_liftList___rarg(lean_object*, lean_object*);
lean_object* l_liftT___rarg(lean_object*, lean_object*);
lean_object* l_coeBaseAux___rarg(lean_object*);
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
lean_object* l_coeB___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeB(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeB___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeT___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeT___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeFnB___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeFnB(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeFnB___rarg), 2, 0);
return x_2;
}
}
lean_object* l_coe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coe___rarg), 2, 0);
return x_3;
}
}
lean_object* l_coeFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeFn___rarg), 2, 0);
return x_2;
}
}
lean_object* l_coeSort___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_coeSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeSort___rarg), 2, 0);
return x_2;
}
}
lean_object* l_liftTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_liftTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_liftTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* _init_l_liftRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_liftRefl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_liftRefl___closed__1;
return x_2;
}
}
lean_object* l_coeTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_coeTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeTrans___rarg), 3, 0);
return x_4;
}
}
lean_object* l_coeBase___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeB___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_coeBase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeBase___rarg), 1, 0);
return x_3;
}
}
lean_object* l_coeOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_coeOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeOption___rarg), 1, 0);
return x_2;
}
}
lean_object* l_coeTransAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_coeTransAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_coeTransAux___rarg), 3, 0);
return x_4;
}
}
lean_object* l_coeBaseAux___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeB___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_coeBaseAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeBaseAux___rarg), 1, 0);
return x_3;
}
}
lean_object* l_coeFnTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_coeFnTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeFnTrans___rarg), 3, 0);
return x_3;
}
}
lean_object* l_coeSortTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_coeSortTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeSortTrans___rarg), 3, 0);
return x_3;
}
}
lean_object* l_coeToLift___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_coeT___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_coeToLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeToLift___rarg), 1, 0);
return x_3;
}
}
lean_object* _init_l_coeBoolToProp() {
_start:
{
return lean_box(0);
}
}
lean_object* _init_l_coeSortBool() {
_start:
{
return lean_box(0);
}
}
uint8_t l_coeDecidableEq(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 1;
x_3 = l_Bool_DecidableEq(x_1, x_2);
return x_3;
}
}
lean_object* l_coeDecidableEq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_coeDecidableEq(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_coeSubtype___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_coeSubtype(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_coeSubtype___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_coeSubtype___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_coeSubtype___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_coeSubtype___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_coeSubtype(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_liftFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_1(x_3, x_5);
x_7 = lean_apply_1(x_1, x_6);
return x_7;
}
}
lean_object* l_liftFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_liftFn___rarg), 4, 0);
return x_5;
}
}
lean_object* l_liftFnRange___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_liftFnRange(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_liftFnRange___rarg), 3, 0);
return x_4;
}
}
lean_object* l_liftFnDom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
lean_object* l_liftFnDom(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_liftFnDom___rarg), 3, 0);
return x_4;
}
}
lean_object* l_liftPair___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_liftPair(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_liftPair___rarg), 3, 0);
return x_5;
}
}
lean_object* l_liftPair_u2081___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_liftPair_u2081(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_liftPair_u2081___rarg), 2, 0);
return x_4;
}
}
lean_object* l_liftPair_u2082___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_liftPair_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_liftPair_u2082___rarg), 2, 0);
return x_4;
}
}
lean_object* l_List_map___main___at_liftList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_List_map___main___at_liftList___spec__1___rarg(x_1, x_6);
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
x_12 = l_List_map___main___at_liftList___spec__1___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at_liftList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_map___main___at_liftList___spec__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_liftList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_liftList___spec__1___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_liftList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_liftList___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_List_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Coe(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_liftRefl___closed__1 = _init_l_liftRefl___closed__1();
lean_mark_persistent(l_liftRefl___closed__1);
l_coeBoolToProp = _init_l_coeBoolToProp();
l_coeSortBool = _init_l_coeSortBool();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif

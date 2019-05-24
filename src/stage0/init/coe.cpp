// Lean compiler output
// Module: init.coe
// Imports: init.data.list.basic
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
obj* l_coe___rarg(obj*, obj*);
obj* l_liftPair_u2081(obj*, obj*, obj*);
obj* l_coe(obj*, obj*);
obj* l_liftTrans___rarg(obj*, obj*, obj*);
obj* l_coeTransAux___rarg(obj*, obj*, obj*);
obj* l_liftPair_u2081___rarg(obj*, obj*);
obj* l_coeFnB___rarg(obj*, obj*);
obj* l_coeSortTrans___rarg(obj*, obj*, obj*);
obj* l_coeDecidableEq___boxed(obj*);
obj* l_coeBaseAux(obj*, obj*);
obj* l_coeFn___rarg(obj*, obj*);
obj* l_liftFnDom(obj*, obj*, obj*);
obj* l_coeSort___rarg(obj*, obj*);
obj* l_liftPair_u2082___rarg(obj*, obj*);
obj* l_liftRefl(obj*);
obj* l_coeSortTrans(obj*, obj*);
obj* l_liftT___rarg(obj*, obj*);
obj* l_liftList(obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_coeFnB(obj*);
obj* l_liftFn(obj*, obj*, obj*, obj*);
obj* l_liftTrans(obj*, obj*, obj*);
obj* l_liftPair(obj*, obj*, obj*, obj*);
obj* l_coeSubtype(obj*, obj*);
obj* l_coeToLift(obj*, obj*);
obj* l_liftT(obj*, obj*);
obj* l_liftFnRange___rarg(obj*, obj*, obj*);
obj* l_coeBoolToProp;
obj* l_coeB(obj*, obj*);
obj* l_coeTransAux(obj*, obj*, obj*);
obj* l_coeSubtype___rarg(obj*);
obj* l_coeSortBool;
obj* l_coeFnTrans(obj*, obj*);
obj* l_lift___rarg(obj*, obj*);
obj* l_coeOption___rarg(obj*);
obj* l_coeFn(obj*);
obj* l_coeB___rarg(obj*, obj*);
obj* l_coeBase(obj*, obj*);
obj* l_coeOption(obj*);
uint8 l_coeDecidableEq(uint8);
obj* l_liftRefl___closed__1;
obj* l_coeSubtype___boxed(obj*, obj*);
obj* l_liftFnDom___rarg(obj*, obj*, obj*);
obj* l_coeTrans(obj*, obj*, obj*);
obj* l_coeSubtype___rarg___boxed(obj*);
obj* l_liftPair___rarg(obj*, obj*, obj*);
obj* l_List_map___main___at_liftList___spec__1___rarg(obj*, obj*);
obj* l_liftFnRange(obj*, obj*, obj*);
obj* l_coeTrans___rarg(obj*, obj*, obj*);
obj* l_List_map___main___at_liftList___spec__1(obj*, obj*);
obj* l_coeT___rarg(obj*, obj*);
obj* l_coeSort(obj*);
obj* l_coeToLift___rarg(obj*);
obj* l_liftList___rarg(obj*, obj*);
obj* l_liftPair_u2082(obj*, obj*, obj*);
obj* l_coeBase___rarg(obj*);
obj* l_coeT(obj*, obj*);
obj* l_coeBaseAux___rarg(obj*);
obj* l_liftFn___rarg(obj*, obj*, obj*, obj*);
obj* l_lift(obj*, obj*);
obj* l_coeFnTrans___rarg(obj*, obj*, obj*);
obj* l_lift___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_lift(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lift___rarg), 2, 0);
return x_3;
}
}
obj* l_liftT___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_liftT(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_liftT___rarg), 2, 0);
return x_3;
}
}
obj* l_coeB___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coeB(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeB___rarg), 2, 0);
return x_3;
}
}
obj* l_coeT___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coeT(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeT___rarg), 2, 0);
return x_3;
}
}
obj* l_coeFnB___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coeFnB(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeFnB___rarg), 2, 0);
return x_2;
}
}
obj* l_coe___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coe(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coe___rarg), 2, 0);
return x_3;
}
}
obj* l_coeFn___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coeFn(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeFn___rarg), 2, 0);
return x_2;
}
}
obj* l_coeSort___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::apply_1(x_1, x_2);
return x_3;
}
}
obj* l_coeSort(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeSort___rarg), 2, 0);
return x_2;
}
}
obj* l_liftTrans___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_liftTrans(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_liftTrans___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_liftRefl___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_liftRefl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_liftRefl___closed__1;
return x_2;
}
}
obj* l_coeTrans___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_coeTrans(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coeTrans___rarg), 3, 0);
return x_4;
}
}
obj* l_coeBase___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeB___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_coeBase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeBase___rarg), 1, 0);
return x_3;
}
}
obj* l_coeOption___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_coeOption(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeOption___rarg), 1, 0);
return x_2;
}
}
obj* l_coeTransAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_coeTransAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coeTransAux___rarg), 3, 0);
return x_4;
}
}
obj* l_coeBaseAux___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeB___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_coeBaseAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeBaseAux___rarg), 1, 0);
return x_3;
}
}
obj* l_coeFnTrans___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_coeFnTrans(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeFnTrans___rarg), 3, 0);
return x_3;
}
}
obj* l_coeSortTrans___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_coeSortTrans(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeSortTrans___rarg), 3, 0);
return x_3;
}
}
obj* l_coeToLift___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_coeT___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_coeToLift(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeToLift___rarg), 1, 0);
return x_3;
}
}
obj* _init_l_coeBoolToProp() {
_start:
{
return lean::box(0);
}
}
obj* _init_l_coeSortBool() {
_start:
{
return lean::box(0);
}
}
uint8 l_coeDecidableEq(uint8 x_1) {
_start:
{
if (x_1 == 0)
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
obj* l_coeDecidableEq___boxed(obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_coeDecidableEq(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_coeSubtype___rarg(obj* x_1) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_coeSubtype(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coeSubtype___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_coeSubtype___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_coeSubtype___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_coeSubtype___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_coeSubtype(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_liftFn___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::apply_1(x_3, x_5);
x_7 = lean::apply_1(x_2, x_6);
return x_7;
}
}
obj* l_liftFn(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_liftFn___rarg), 4, 0);
return x_5;
}
}
obj* l_liftFnRange___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* l_liftFnRange(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_liftFnRange___rarg), 3, 0);
return x_4;
}
}
obj* l_liftFnDom___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_liftFnDom(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_liftFnDom___rarg), 3, 0);
return x_4;
}
}
obj* l_liftPair___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = lean::apply_1(x_2, x_6);
lean::cnstr_set(x_3, 1, x_8);
lean::cnstr_set(x_3, 0, x_7);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_3);
x_11 = lean::apply_1(x_1, x_9);
x_12 = lean::apply_1(x_2, x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_liftPair(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_liftPair___rarg), 3, 0);
return x_5;
}
}
obj* l_liftPair_u2081___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::apply_1(x_1, x_4);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_2);
x_8 = lean::apply_1(x_1, x_6);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
}
}
obj* l_liftPair_u2081(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_liftPair_u2081___rarg), 2, 0);
return x_4;
}
}
obj* l_liftPair_u2082___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::apply_1(x_1, x_4);
lean::cnstr_set(x_2, 1, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_2);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_liftPair_u2082(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_liftPair_u2082___rarg), 2, 0);
return x_4;
}
}
obj* l_List_map___main___at_liftList___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = l_List_map___main___at_liftList___spec__1___rarg(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_9);
x_12 = l_List_map___main___at_liftList___spec__1___rarg(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_List_map___main___at_liftList___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_liftList___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_liftList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_map___main___at_liftList___spec__1___rarg(x_1, x_2);
return x_3;
}
}
obj* l_liftList(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_liftList___rarg), 2, 0);
return x_3;
}
}
obj* initialize_init_data_list_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_coe(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
l_liftRefl___closed__1 = _init_l_liftRefl___closed__1();
lean::mark_persistent(l_liftRefl___closed__1);
l_coeBoolToProp = _init_l_coeBoolToProp();
l_coeSortBool = _init_l_coeSortBool();
return w;
}

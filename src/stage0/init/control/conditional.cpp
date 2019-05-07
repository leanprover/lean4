// Lean compiler output
// Module: init.control.conditional
// Imports: init.control.monad init.data.option.basic
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
obj* l_bool___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_andM___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Option_HasToBool___boxed(obj*);
obj* l_bool___rarg(obj*, obj*, obj*, obj*);
obj* l_orM___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_bool(obj*, obj*);
obj* l_bool___boxed(obj*, obj*);
obj* l_Bool_HasToBool;
obj* l_notM___boxed(obj*);
obj* l_orM___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Option_HasToBool___closed__1;
obj* l_notM___rarg___closed__1;
obj* l_Option_toBool___rarg___boxed(obj*);
obj* l_andM___boxed(obj*, obj*);
obj* l_andM___rarg(obj*, obj*, obj*, obj*);
obj* l_Option_HasToBool(obj*);
obj* l_notM(obj*);
obj* l_notM___rarg(obj*, obj*);
obj* l_notM___rarg___lambda__1___boxed(obj*);
obj* l_andM(obj*, obj*);
obj* l_orM(obj*, obj*);
uint8 l_notM___rarg___lambda__1(uint8);
obj* l_andM___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_orM___rarg(obj*, obj*, obj*, obj*);
obj* l_orM___boxed(obj*, obj*);
obj* _init_l_Bool_HasToBool() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Option_HasToBool___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toBool___rarg___boxed), 1, 0);
return x_0;
}
}
obj* l_Option_HasToBool(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_HasToBool___closed__1;
return x_1;
}
}
obj* l_Option_HasToBool___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_HasToBool(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_bool___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::apply_1(x_0, x_3);
x_5 = lean::unbox(x_4);
if (x_5 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l_bool(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bool___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_bool___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_bool___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_bool___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_bool(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_orM___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; uint8 x_6; 
lean::inc(x_3);
x_5 = lean::apply_1(x_0, x_3);
x_6 = lean::unbox(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_10; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), x_3);
return x_16;
}
}
}
obj* l_orM___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_orM___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_3);
lean::closure_set(x_6, 2, x_0);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_orM(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_orM___rarg), 4, 0);
return x_2;
}
}
obj* l_orM___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_orM___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_orM___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_orM(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_andM___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; uint8 x_6; 
lean::inc(x_3);
x_5 = lean::apply_1(x_0, x_3);
x_6 = lean::unbox(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_10; obj* x_13; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::apply_2(x_10, lean::box(0), x_3);
return x_13;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_andM___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_andM___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_0);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_andM(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_andM___rarg), 4, 0);
return x_2;
}
}
obj* l_andM___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_andM___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_andM___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_andM(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_notM___rarg___lambda__1(uint8 x_0) {
_start:
{
if (x_0 == 0)
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
obj* _init_l_notM___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_notM___rarg___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* l_notM___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_notM___rarg___closed__1;
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_1);
return x_9;
}
}
obj* l_notM(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_notM___rarg), 2, 0);
return x_1;
}
}
obj* l_notM___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_notM___rarg___lambda__1(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_notM___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_notM(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_control_monad(obj*);
obj* initialize_init_data_option_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_conditional(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
 l_Bool_HasToBool = _init_l_Bool_HasToBool();
lean::mark_persistent(l_Bool_HasToBool);
 l_Option_HasToBool___closed__1 = _init_l_Option_HasToBool___closed__1();
lean::mark_persistent(l_Option_HasToBool___closed__1);
 l_notM___rarg___closed__1 = _init_l_notM___rarg___closed__1();
lean::mark_persistent(l_notM___rarg___closed__1);
return w;
}

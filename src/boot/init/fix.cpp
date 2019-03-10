// Lean compiler output
// Module: init.fix
// Imports: init.data.uint
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
obj* l_fix___rarg___lambda__1___boxed(obj*, obj*);
obj* l_fix___rarg(obj*, obj*, obj*);
obj* l_bfix___main(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_bfix___rarg(obj*, obj*, obj*, obj*);
obj* l_bfix___main___rarg(obj*, obj*, obj*, obj*);
obj* l_bfix(obj*, obj*);
obj* l_fix(obj*, obj*);
obj* l_fix___rarg___lambda__1(obj*, obj*);
obj* l_fix__core___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_bfix___main___boxed(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_bfix___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_fix___boxed(obj*, obj*);
obj* l_bfix___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_bfix___boxed(obj*, obj*);
obj* l_bfix___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::inc(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix___main___rarg___boxed), 4, 3);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::apply_2(x_1, x_9, x_3);
return x_10;
}
else
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::apply_1(x_0, x_3);
return x_12;
}
}
}
obj* l_bfix___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_bfix___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_bfix___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_bfix___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_bfix___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_bfix___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_bfix___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_bfix(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_bfix___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_bfix___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_bfix___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_bfix(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_fix__core___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::fixpoint(x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_fix___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_fix___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_fix___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::fixpoint(x_1, x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_fix(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fix___rarg), 3, 0);
return x_2;
}
}
obj* l_fix___rarg___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_fix___rarg___lambda__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_fix___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_fix(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
void initialize_init_data_uint();
static bool _G_initialized = false;
void initialize_init_fix() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_uint();
}

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
obj* l_bfix4___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix1(obj*, obj*);
obj* l_bfix3___main(obj*, obj*, obj*, obj*);
obj* l_fixCore4(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore___rarg___boxed(obj*, obj*, obj*);
obj* l_bfix3___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix5___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_bfix2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_fix1___rarg(obj*, obj*, obj*);
obj* l_bfix6(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix2(obj*, obj*, obj*);
obj* l_bfix6___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix4___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix5___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix4___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_fix2(obj*, obj*, obj*);
obj* l_bfix3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix4___main(obj*, obj*, obj*, obj*, obj*);
obj* l_bfix5___main(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix2___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_fix1___rarg___lambda__1(obj*, obj*);
obj* l_bfix6___main(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix3(obj*, obj*, obj*, obj*);
obj* l_fixCore6(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix1___rarg___lambda__1___boxed(obj*, obj*);
obj* l_bfix6___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix4(obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix5___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix2___rarg___lambda__1(obj*, obj*, obj*);
obj* l_fix___rarg(obj*, obj*, obj*);
obj* l_fix6___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix6___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_fix5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore___rarg(obj*, obj*, obj*);
obj* l_fix(obj*, obj*);
obj* l_fix6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix3___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_fix4(obj*, obj*, obj*, obj*, obj*);
obj* l_bfix1___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_fixCore1(obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore(obj*, obj*);
obj* l_fix1(obj*, obj*);
obj* l_bfix5___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix4___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix1___main(obj*, obj*);
obj* l_fixCore3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix6(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix2___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_bfix2___main(obj*, obj*, obj*);
obj* l_fix2___rarg(obj*, obj*, obj*, obj*);
obj* l_fixCore6___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix5___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fixCore5(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix3___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix1___main___rarg(obj*, obj*, obj*, obj*);
obj* l_fixCore1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_bfix1___rarg(obj*, obj*, obj*, obj*);
obj* l_bfix4___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_bfix3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_fix3___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_bfix6___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_fix4___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_bfix3(obj*, obj*, obj*, obj*);
obj* l_fix4___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_fix2___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_bfix1___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
lean::inc(x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix1___main___rarg___boxed), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::apply_2(x_2, x_9, x_4);
return x_10;
}
else
{
obj* x_11; 
lean::dec(x_2);
x_11 = lean::apply_1(x_1, x_4);
return x_11;
}
}
}
obj* l_bfix1___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix1___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_bfix1___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_bfix1___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_bfix1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_bfix1___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_bfix1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix1___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_bfix1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_bfix1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_fixCore1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::fixpoint(x_4, x_5);
return x_6;
}
}
obj* l_fixCore___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::fixpoint(x_2, x_3);
return x_4;
}
}
obj* l_fixCore(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_fixCore___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_fixCore___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_fix1___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_fix1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::fixpoint(x_2, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_fix1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_fix1___rarg), 3, 0);
return x_3;
}
}
obj* l_fix1___rarg___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fix1___rarg___lambda__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_fix___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean::closure_set(x_4, 0, x_1);
x_5 = lean::fixpoint(x_2, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_fix(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_fix___rarg), 3, 0);
return x_3;
}
}
obj* l_bfix2___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::inc(x_2);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix2___main___rarg___boxed), 5, 3);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_9);
x_11 = lean::apply_3(x_2, x_10, x_4, x_5);
return x_11;
}
else
{
obj* x_12; 
lean::dec(x_2);
x_12 = lean::apply_2(x_1, x_4, x_5);
return x_12;
}
}
}
obj* l_bfix2___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix2___main___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_bfix2___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_bfix2___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_bfix2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_bfix2___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_bfix2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix2___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_bfix2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_bfix2___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_fixCore2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::fixpoint2(x_5, x_6, x_7);
return x_8;
}
}
obj* l_fix2___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_fix2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_fix2___rarg___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::fixpoint2(x_2, x_3, x_4);
return x_6;
}
}
obj* l_fix2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_fix2___rarg), 4, 0);
return x_4;
}
}
obj* l_fix2___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_fix2___rarg___lambda__1(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_bfix3___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_3, x_9);
lean::inc(x_2);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix3___main___rarg___boxed), 6, 3);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_2);
lean::closure_set(x_11, 2, x_10);
x_12 = lean::apply_4(x_2, x_11, x_4, x_5, x_6);
return x_12;
}
else
{
obj* x_13; 
lean::dec(x_2);
x_13 = lean::apply_3(x_1, x_4, x_5, x_6);
return x_13;
}
}
}
obj* l_bfix3___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix3___main___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_bfix3___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_bfix3___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_bfix3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_bfix3___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_bfix3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix3___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_bfix3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_bfix3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_fixCore3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = lean::fixpoint3(x_6, x_7, x_8, x_9);
return x_10;
}
}
obj* l_fix3___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_fix3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_fix3___rarg___lambda__1___boxed), 4, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = lean::fixpoint3(x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_fix3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_fix3___rarg), 5, 0);
return x_5;
}
}
obj* l_fix3___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_fix3___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_bfix4___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_3, x_10);
lean::inc(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix4___main___rarg___boxed), 7, 3);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_2);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::apply_5(x_2, x_12, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
obj* x_14; 
lean::dec(x_2);
x_14 = lean::apply_4(x_1, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
obj* l_bfix4___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix4___main___rarg___boxed), 7, 0);
return x_6;
}
}
obj* l_bfix4___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_bfix4___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
return x_8;
}
}
obj* l_bfix4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_bfix4___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_bfix4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix4___rarg___boxed), 7, 0);
return x_6;
}
}
obj* l_bfix4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_bfix4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
return x_8;
}
}
obj* l_fixCore4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11) {
_start:
{
obj* x_12; 
x_12 = lean::fixpoint4(x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
obj* l_fix4___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_fix4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_fix4___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_7, 0, x_1);
x_8 = lean::fixpoint4(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_fix4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_fix4___rarg), 6, 0);
return x_6;
}
}
obj* l_fix4___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_fix4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_bfix5___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_3, x_11);
lean::inc(x_2);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix5___main___rarg___boxed), 8, 3);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::apply_6(x_2, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
obj* x_15; 
lean::dec(x_2);
x_15 = lean::apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
}
obj* l_bfix5___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix5___main___rarg___boxed), 8, 0);
return x_7;
}
}
obj* l_bfix5___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_bfix5___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_3);
return x_9;
}
}
obj* l_bfix5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_bfix5___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
obj* l_bfix5(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix5___rarg___boxed), 8, 0);
return x_7;
}
}
obj* l_bfix5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_bfix5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_3);
return x_9;
}
}
obj* l_fixCore5___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; 
x_14 = lean::fixpoint5(x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
obj* l_fix5___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_fix5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_fix5___rarg___lambda__1___boxed), 6, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = lean::fixpoint5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_fix5(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_fix5___rarg), 7, 0);
return x_7;
}
}
obj* l_fix5___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_fix5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_bfix6___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_3, x_12);
lean::inc(x_2);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix6___main___rarg___boxed), 9, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::apply_7(x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_2);
x_16 = lean::apply_6(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
obj* l_bfix6___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix6___main___rarg___boxed), 9, 0);
return x_8;
}
}
obj* l_bfix6___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_bfix6___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_3);
return x_10;
}
}
obj* l_bfix6___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_bfix6___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
obj* l_bfix6(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_bfix6___rarg___boxed), 9, 0);
return x_8;
}
}
obj* l_bfix6___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_10; 
x_10 = l_bfix6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean::dec(x_3);
return x_10;
}
}
obj* l_fixCore6___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13, obj* x_14, obj* x_15) {
_start:
{
obj* x_16; 
x_16 = lean::fixpoint6(x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
obj* l_fix6___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
lean::inc(x_1);
return x_1;
}
}
obj* l_fix6___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; 
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_fix6___rarg___lambda__1___boxed), 7, 1);
lean::closure_set(x_9, 0, x_1);
x_10 = lean::fixpoint6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
obj* l_fix6(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_fix6___rarg), 8, 0);
return x_8;
}
}
obj* l_fix6___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_fix6___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* initialize_init_data_uint(obj*);
static bool _G_initialized = false;
obj* initialize_init_fix(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
return w;
}

// Lean compiler output
// Module: init.data.nat.basic
// Imports: init.core
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
obj* l_Nat_forCore(obj*);
obj* l_Nat_decLe___boxed(obj*, obj*);
obj* l_Nat_forCore___main(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Nat_forCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Nat_HasPow;
obj* l_Nat_repeatCore___boxed(obj*);
obj* l_Nat_forCore___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Nat_repeat___boxed(obj*);
obj* l_Nat_for___rarg(obj*, obj*, obj*);
obj* l_Nat_forCore___main___rarg___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Nat_forCore___boxed(obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Nat_forCore___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_sub___boxed(obj*, obj*);
obj* l_Nat_mul___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Nat_ble___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Nat_repeatCore___main___rarg(obj*, obj*, obj*);
obj* l_Nat_for___boxed(obj*);
obj* l_Nat_repeatCore___main(obj*);
obj* l_Nat_repeat___rarg(obj*, obj*, obj*);
obj* l_Nat_for(obj*);
obj* l_Nat_pow___main(obj*, obj*);
obj* l_Nat_HasSub;
obj* l_Nat_decLt___boxed(obj*, obj*);
obj* l_Nat_pow___main___boxed(obj*, obj*);
obj* l_Nat_beq___boxed(obj*, obj*);
obj* l_Nat_repeatCore___rarg(obj*, obj*, obj*);
obj* l_Nat_pow(obj*, obj*);
obj* l_Nat_repeatCore___main___boxed(obj*);
obj* l_Nat_pred___boxed(obj*);
obj* l_Nat_HasLessEq;
obj* l_Nat_forCore___main___boxed(obj*);
obj* l_Nat_pow___boxed(obj*, obj*);
obj* l_Nat_HasLess;
obj* l_Nat_HasMul;
obj* l_Nat_repeatCore(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Nat_repeat(obj*);
obj* l_Nat_max___boxed(obj*, obj*);
obj* l_Nat_max(obj*, obj*);
obj* l_Nat_DecidableEq;
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Nat_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Nat_decEq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Nat_DecidableEq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_0;
}
}
obj* l_Nat_ble___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_le(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Nat_HasLessEq() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Nat_HasLess() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_Nat_pred___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat_sub(x_0, lean::box(1));
return x_1;
}
}
obj* l_Nat_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_sub(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_mul(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Nat_HasSub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Nat_HasMul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_Nat_forCore___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_11; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_2, x_6);
x_8 = lean::nat_sub(x_1, x_2);
lean::dec(x_2);
lean::inc(x_0);
x_11 = lean::apply_2(x_0, x_8, x_3);
x_2 = x_7;
x_3 = x_11;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_Nat_forCore___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_forCore___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Nat_forCore___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_forCore___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Nat_forCore___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_forCore___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_forCore___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_forCore___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Nat_forCore(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_forCore___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Nat_forCore___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_forCore___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Nat_forCore___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_forCore(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_for___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_1);
x_4 = l_Nat_forCore___main___rarg(x_0, x_1, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Nat_for(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_for___rarg), 3, 0);
return x_1;
}
}
obj* l_Nat_for___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_for(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_repeatCore___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
lean::inc(x_0);
x_9 = lean::apply_1(x_0, x_2);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_Nat_repeatCore___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeatCore___main___rarg), 3, 0);
return x_1;
}
}
obj* l_Nat_repeatCore___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_repeatCore___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_repeatCore___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_repeatCore___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Nat_repeatCore(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeatCore___rarg), 3, 0);
return x_1;
}
}
obj* l_Nat_repeatCore___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_repeatCore(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_repeat___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_repeatCore___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Nat_repeat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeat___rarg), 3, 0);
return x_1;
}
}
obj* l_Nat_repeat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_repeat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Nat_pow___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_sub(x_1, x_4);
x_6 = l_Nat_pow___main(x_0, x_5);
lean::dec(x_5);
x_8 = lean::nat_mul(x_6, x_0);
lean::dec(x_6);
return x_8;
}
else
{
obj* x_10; 
x_10 = lean::mk_nat_obj(1ul);
return x_10;
}
}
}
obj* l_Nat_pow___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_pow___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_pow(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_pow___main(x_0, x_1);
return x_2;
}
}
obj* l_Nat_pow___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_pow(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Nat_HasPow() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_pow___boxed), 2, 0);
return x_0;
}
}
obj* l_Nat_decLe___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_le(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Nat_decLt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::nat_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Nat_max(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
if (x_2 == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Nat_max___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_max(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_core(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_nat_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
 l_Nat_DecidableEq = _init_l_Nat_DecidableEq();
lean::mark_persistent(l_Nat_DecidableEq);
 l_Nat_HasLessEq = _init_l_Nat_HasLessEq();
lean::mark_persistent(l_Nat_HasLessEq);
 l_Nat_HasLess = _init_l_Nat_HasLess();
lean::mark_persistent(l_Nat_HasLess);
 l_Nat_HasSub = _init_l_Nat_HasSub();
lean::mark_persistent(l_Nat_HasSub);
 l_Nat_HasMul = _init_l_Nat_HasMul();
lean::mark_persistent(l_Nat_HasMul);
 l_Nat_HasPow = _init_l_Nat_HasPow();
lean::mark_persistent(l_Nat_HasPow);
return w;
}

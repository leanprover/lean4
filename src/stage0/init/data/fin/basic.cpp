// Lean compiler output
// Module: init.data.fin.basic
// Imports: init.data.nat.div init.data.nat.bitwise
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
obj* l_Fin_HasZero___boxed(obj*);
obj* l_Fin_HasLess___boxed(obj*);
obj* l_Fin_elim0___boxed(obj*, obj*);
obj* l_Fin_add___main(obj*, obj*, obj*);
obj* l_Fin_decLt(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Fin_land(obj*, obj*, obj*);
obj* l_Fin_mul___main___boxed(obj*, obj*, obj*);
uint8 l_Fin_decLe___rarg(obj*, obj*);
obj* l_Fin_modn___main___boxed(obj*, obj*, obj*);
uint8 l_Fin_DecidableEq___rarg(obj*, obj*);
obj* l_Fin_sub___main___boxed(obj*, obj*, obj*);
obj* l_Fin_lor___main(obj*, obj*, obj*);
obj* l_Fin_lor(obj*, obj*, obj*);
obj* l_Fin_add(obj*, obj*, obj*);
obj* l_Fin_HasModn(obj*);
obj* l_Fin_mul(obj*, obj*, obj*);
obj* l_Fin_HasDiv(obj*);
obj* l_Fin_HasSub(obj*);
obj* l_Fin_decLe(obj*);
obj* l_Fin_modn___boxed(obj*, obj*, obj*);
obj* l_Fin_elim0___main___boxed(obj*, obj*);
obj* l_Fin_DecidableEq___rarg___boxed(obj*, obj*);
obj* l_Fin_modn(obj*, obj*, obj*);
obj* l_Fin_mod___main(obj*, obj*, obj*);
obj* l_Fin_HasAdd(obj*);
obj* l_Fin_decLe___boxed(obj*);
obj* l_Fin_div(obj*, obj*, obj*);
obj* l_Fin_lor___main___boxed(obj*, obj*, obj*);
obj* l_Fin_land___main___boxed(obj*, obj*, obj*);
obj* l_Fin_elim0(obj*, obj*);
obj* l_Fin_sub(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Fin_HasLessEq(obj*);
obj* l_Fin_elim0___main(obj*, obj*);
obj* l_Fin_DecidableEq___boxed(obj*);
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_Fin_div___main___boxed(obj*, obj*, obj*);
obj* l_Fin_DecidableEq(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Fin_mod___boxed(obj*, obj*, obj*);
obj* l_Fin_land___boxed(obj*, obj*, obj*);
obj* l_Fin_mod(obj*, obj*, obj*);
obj* l_Fin_HasMod(obj*);
obj* l_Fin_div___main(obj*, obj*, obj*);
obj* l_Fin_div___boxed(obj*, obj*, obj*);
obj* l_Fin_sub___boxed(obj*, obj*, obj*);
obj* l_Fin_decLt___boxed(obj*);
obj* l_Fin_add___main___boxed(obj*, obj*, obj*);
obj* l_Fin_sub___main(obj*, obj*, obj*);
obj* l_Fin_HasMul(obj*);
obj* l_Fin_decLe___rarg___boxed(obj*, obj*);
obj* l_Fin_HasOne(obj*);
obj* l_Fin_decLt___rarg___boxed(obj*, obj*);
obj* l_Fin_ofNat(obj*, obj*);
uint8 l_Fin_decLt___rarg(obj*, obj*);
namespace lean {
obj* nat_land(obj*, obj*);
}
obj* l_Fin_land___main(obj*, obj*, obj*);
obj* l_Fin_HasLessEq___boxed(obj*);
obj* l_Fin_lor___boxed(obj*, obj*, obj*);
obj* l_Fin_mul___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Fin_modn___main(obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Fin_ofNat___boxed(obj*, obj*);
obj* l_Fin_mod___main___boxed(obj*, obj*, obj*);
obj* l_Fin_HasZero(obj*);
obj* l_Fin_add___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Fin_HasOne___boxed(obj*);
obj* l_Fin_HasLess(obj*);
namespace lean {
obj* nat_lor(obj*, obj*);
}
obj* l_Fin_mul___main(obj*, obj*, obj*);
obj* l_Fin_HasLess(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Fin_HasLess___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_HasLess(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Fin_HasLessEq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Fin_HasLessEq___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_HasLessEq(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Fin_decLt___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_lt(x_1, x_2);
return x_3;
}
}
obj* l_Fin_decLt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_decLt___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Fin_decLt___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Fin_decLt___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Fin_decLt___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_decLt(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Fin_decLe___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_le(x_1, x_2);
return x_3;
}
}
obj* l_Fin_decLe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_decLe___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Fin_decLe___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Fin_decLe___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Fin_decLe___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_decLe(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Fin_elim0___main(obj* x_1, obj* x_2) {
_start:
{
lean_unreachable();
}
}
obj* l_Fin_elim0___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Fin_elim0___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Fin_elim0(obj* x_1, obj* x_2) {
_start:
{
lean_unreachable();
}
}
obj* l_Fin_elim0___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Fin_elim0(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Fin_ofNat(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_add(x_1, x_3);
x_5 = lean::nat_mod(x_2, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_ofNat___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Fin_ofNat(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Fin_add___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_add(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_add___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_add___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_add(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_add___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_add___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_add(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_mul___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_mul(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_mul___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_mul___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_mul(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_mul___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_mul___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_mul(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_sub___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::nat_sub(x_1, x_3);
x_5 = lean::nat_add(x_2, x_4);
lean::dec(x_4);
x_6 = lean::nat_mod(x_5, x_1);
lean::dec(x_5);
return x_6;
}
}
obj* l_Fin_sub___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_sub___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_sub(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_sub___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_sub___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_sub(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_mod___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_mod(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_mod___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_mod___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_mod(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_mod___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_mod___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_mod(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_div___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_div(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_div___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_div___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_div(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_div___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_div___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_div(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_modn___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_mod(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_modn___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_modn___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_modn(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_modn___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_modn___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_modn(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_land___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_land(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_land___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_land___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_land(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_land___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_land___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_land(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_lor___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::nat_lor(x_2, x_3);
x_5 = lean::nat_mod(x_4, x_1);
lean::dec(x_4);
return x_5;
}
}
obj* l_Fin_lor___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_lor___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_lor(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_lor___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Fin_lor___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Fin_lor(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Fin_HasZero(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::mk_nat_obj(0u);
return x_2;
}
}
obj* l_Fin_HasZero___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_HasZero(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Fin_HasOne(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(1u);
x_3 = l_Fin_ofNat(x_1, x_2);
return x_3;
}
}
obj* l_Fin_HasOne___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_HasOne(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Fin_HasAdd(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_add___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Fin_HasSub(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_sub___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Fin_HasMul(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_mul___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Fin_HasMod(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_mod___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Fin_HasDiv(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_div___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Fin_HasModn(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_modn___boxed), 3, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
uint8 l_Fin_DecidableEq___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
obj* l_Fin_DecidableEq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Fin_DecidableEq___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Fin_DecidableEq___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Fin_DecidableEq___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Fin_DecidableEq___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Fin_DecidableEq(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_nat_div(obj*);
obj* initialize_init_data_nat_bitwise(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_fin_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_bitwise(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasLess"), 1, l_Fin_HasLess___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasLessEq"), 1, l_Fin_HasLessEq___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "decLt"), 1, l_Fin_decLt___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "decLe"), 1, l_Fin_decLe___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "elim0"), 2, l_Fin_elim0___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "ofNat"), 2, l_Fin_ofNat___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "add"), 3, l_Fin_add___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "mul"), 3, l_Fin_mul___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "sub"), 3, l_Fin_sub___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "mod"), 3, l_Fin_mod___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "div"), 3, l_Fin_div___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "modn"), 3, l_Fin_modn___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "land"), 3, l_Fin_land___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "lor"), 3, l_Fin_lor___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasZero"), 1, l_Fin_HasZero___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasOne"), 1, l_Fin_HasOne___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasAdd"), 1, l_Fin_HasAdd);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasSub"), 1, l_Fin_HasSub);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasMul"), 1, l_Fin_HasMul);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasMod"), 1, l_Fin_HasMod);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasDiv"), 1, l_Fin_HasDiv);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "HasModn"), 1, l_Fin_HasModn);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Fin"), "DecidableEq"), 1, l_Fin_DecidableEq___boxed);
return w;
}

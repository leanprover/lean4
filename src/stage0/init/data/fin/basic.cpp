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
obj* l_fin_elim0(obj*, obj*);
obj* l_fin_has__lt(obj*);
obj* l_fin_dec__lt___boxed(obj*);
obj* l_fin_of__nat___boxed(obj*, obj*);
obj* l_fin_modn(obj*, obj*, obj*);
obj* l_fin_has__one(obj*);
obj* l_fin_elim0___main(obj*, obj*);
uint8 l_fin_dec__lt___rarg(obj*, obj*);
extern obj* l_nat_lor___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_fin_lor___main(obj*, obj*, obj*);
obj* l_fin_mod(obj*, obj*, obj*);
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_fin_add___main___boxed(obj*, obj*, obj*);
uint8 l_fin_dec__le___rarg(obj*, obj*);
obj* l_fin_has__le(obj*);
obj* l_nat_bitwise___main(obj*, obj*, obj*);
obj* l_fin_sub___boxed(obj*, obj*, obj*);
obj* l_fin_sub(obj*, obj*, obj*);
obj* l_fin_decidable__eq(obj*);
obj* l_fin_modn___boxed(obj*, obj*, obj*);
obj* l_fin_has__le___boxed(obj*);
obj* l_fin_land(obj*, obj*, obj*);
obj* l_fin_lor___boxed(obj*, obj*, obj*);
obj* l_fin_mod___main___boxed(obj*, obj*, obj*);
obj* l_fin_mod___main(obj*, obj*, obj*);
obj* l_fin_mul___boxed(obj*, obj*, obj*);
obj* l_fin_mod___boxed(obj*, obj*, obj*);
obj* l_fin_mul___main___boxed(obj*, obj*, obj*);
obj* l_fin_add(obj*, obj*, obj*);
obj* l_fin_has__lt___boxed(obj*);
obj* l_fin_decidable__eq___boxed(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_fin_has__one___boxed(obj*);
obj* l_fin_sub___main___boxed(obj*, obj*, obj*);
obj* l_fin_add___main(obj*, obj*, obj*);
obj* l_fin_of__nat(obj*, obj*);
obj* l_fin_has__zero___boxed(obj*);
obj* l_fin_add___boxed(obj*, obj*, obj*);
obj* l_fin_div___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_fin_elim0___main___boxed(obj*, obj*);
obj* l_fin_has__sub(obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_fin_elim0___boxed(obj*, obj*);
obj* l_fin_mul___main(obj*, obj*, obj*);
obj* l_fin_modn___main___boxed(obj*, obj*, obj*);
obj* l_fin_has__div(obj*);
obj* l_fin_dec__le(obj*);
obj* l_fin_has__zero(obj*);
obj* l_fin_decidable__eq___rarg___boxed(obj*, obj*);
extern obj* l_nat_land___closed__1;
obj* l_fin_sub___main(obj*, obj*, obj*);
obj* l_fin_mul(obj*, obj*, obj*);
obj* l_fin_has__modn(obj*);
obj* l_fin_dec__le___rarg___boxed(obj*, obj*);
obj* l_fin_dec__lt(obj*);
obj* l_fin_dec__le___boxed(obj*);
obj* l_fin_land___main(obj*, obj*, obj*);
obj* l_fin_land___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_fin_div___main(obj*, obj*, obj*);
obj* l_fin_land___boxed(obj*, obj*, obj*);
obj* l_fin_dec__lt___rarg___boxed(obj*, obj*);
obj* l_fin_lor___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_fin_has__mod(obj*);
obj* l_fin_has__mul(obj*);
obj* l_fin_modn___main(obj*, obj*, obj*);
obj* l_fin_div(obj*, obj*, obj*);
obj* l_fin_has__add(obj*);
obj* l_fin_div___main___boxed(obj*, obj*, obj*);
obj* l_fin_lor(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
uint8 l_fin_decidable__eq___rarg(obj*, obj*);
obj* l_fin_has__lt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_fin_has__lt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_has__lt(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_fin_has__le(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_fin_has__le___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_has__le(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_fin_dec__lt___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_fin_dec__lt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_dec__lt___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_fin_dec__lt___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_fin_dec__lt___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_fin_dec__lt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_dec__lt(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_fin_dec__le___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
return x_2;
}
}
obj* l_fin_dec__le(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_dec__le___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_fin_dec__le___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_fin_dec__le___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_fin_dec__le___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_dec__le(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_fin_elim0___main(obj* x_0, obj* x_1) {
_start:
{
lean_unreachable();
}
}
obj* l_fin_elim0___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_fin_elim0___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_fin_elim0(obj* x_0, obj* x_1) {
_start:
{
lean_unreachable();
}
}
obj* l_fin_elim0___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_fin_elim0(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_fin_of__nat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_0, x_2);
x_4 = lean::nat_mod(x_1, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_fin_of__nat___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_fin_of__nat(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_fin_add___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::nat_mod(x_3, x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_fin_add___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_add___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_add(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_add___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_add___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_add(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_mul___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::nat_mul(x_1, x_2);
x_4 = lean::nat_mod(x_3, x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_fin_mul___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_mul___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_mul(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_mul___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_mul___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_mul(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_sub___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; 
x_3 = lean::nat_sub(x_0, x_2);
x_4 = lean::nat_add(x_1, x_3);
lean::dec(x_3);
x_6 = lean::nat_mod(x_4, x_0);
lean::dec(x_4);
return x_6;
}
}
obj* l_fin_sub___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_sub___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_sub(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_sub___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_sub___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_sub(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_mod___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::nat_mod(x_1, x_2);
x_4 = lean::nat_mod(x_3, x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_fin_mod___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_mod___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_mod(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_mod___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_mod___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_mod(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_div___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::nat_div(x_1, x_2);
x_4 = lean::nat_mod(x_3, x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_fin_div___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_div___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_div(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_div___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_div___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_div(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_modn___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::nat_mod(x_1, x_2);
x_4 = lean::nat_mod(x_3, x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l_fin_modn___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_modn___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_modn(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_modn___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_modn___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_modn(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_land___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_nat_land___closed__1;
x_4 = l_nat_bitwise___main(x_3, x_1, x_2);
x_5 = lean::nat_mod(x_4, x_0);
lean::dec(x_4);
return x_5;
}
}
obj* l_fin_land___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_land___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_land(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_land___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_land___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_land(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_lor___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_nat_lor___closed__1;
x_4 = l_nat_bitwise___main(x_3, x_1, x_2);
x_5 = lean::nat_mod(x_4, x_0);
lean::dec(x_4);
return x_5;
}
}
obj* l_fin_lor___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_lor___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_lor(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_lor___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_fin_lor___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_fin_lor(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_fin_has__zero(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0u);
return x_1;
}
}
obj* l_fin_has__zero___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_has__zero(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_fin_has__one(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1u);
x_2 = l_fin_of__nat(x_0, x_1);
return x_2;
}
}
obj* l_fin_has__one___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_has__one(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_fin_has__add(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_add___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__sub(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_sub___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__mul(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_mul___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__mod(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_mod___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__div(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_div___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__modn(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_modn___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
uint8 l_fin_decidable__eq___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
obj* l_fin_decidable__eq(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_decidable__eq___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_fin_decidable__eq___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_fin_decidable__eq___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_fin_decidable__eq___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_decidable__eq(x_0);
lean::dec(x_0);
return x_1;
}
}
void initialize_init_data_nat_div();
void initialize_init_data_nat_bitwise();
static bool _G_initialized = false;
void initialize_init_data_fin_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_div();
 initialize_init_data_nat_bitwise();
}

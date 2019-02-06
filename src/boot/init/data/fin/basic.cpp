// Lean compiler output
// Module: init.data.fin.basic
// Imports: init.data.nat.div
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_fin_modn(obj*, obj*, obj*);
obj* l_fin_has__one(obj*);
obj* l_fin_elim0___main(obj*, obj*);
uint8 l_fin_dec__lt___rarg(obj*, obj*);
obj* l_fin_mod(obj*, obj*, obj*);
obj* l_fin_le;
uint8 l_fin_dec__le___rarg(obj*, obj*);
obj* l_fin_has__le(obj*);
obj* l_fin_sub(obj*, obj*, obj*);
obj* l_fin_decidable__eq(obj*);
obj* l_fin_mod___main(obj*, obj*, obj*);
obj* l_fin_lt;
obj* l_fin_add(obj*, obj*, obj*);
obj* l_fin_add___main(obj*, obj*, obj*);
obj* l_fin_of__nat(obj*, obj*);
obj* l_fin_has__sub(obj*);
obj* l_fin_mul___main(obj*, obj*, obj*);
obj* l_fin_has__div(obj*);
obj* l_fin_dec__le(obj*);
obj* l_fin_has__zero(obj*);
obj* l_fin_decidable__eq___rarg___boxed(obj*, obj*);
obj* l_fin_sub___main(obj*, obj*, obj*);
obj* l_fin_mul(obj*, obj*, obj*);
obj* l_fin_has__modn(obj*);
obj* l_fin_dec__le___rarg___boxed(obj*, obj*);
obj* l_fin_dec__lt(obj*);
obj* l_fin_div___main(obj*, obj*, obj*);
obj* l_fin_dec__lt___rarg___boxed(obj*, obj*);
obj* l_fin_has__mod(obj*);
obj* l_fin_has__mul(obj*);
obj* l_fin_modn___main(obj*, obj*, obj*);
obj* l_fin_div(obj*, obj*, obj*);
obj* l_fin_has__add(obj*);
uint8 l_fin_decidable__eq___rarg(obj*, obj*);
obj* _init_l_fin_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_fin_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_fin_has__lt(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
}
obj* l_fin_has__le(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
}
uint8 l_fin_dec__lt___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_fin_dec__lt(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_dec__lt___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_fin_dec__lt___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_fin_dec__lt___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_fin_dec__le___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_fin_dec__le(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_dec__le___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_fin_dec__le___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_fin_dec__le___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_fin_elim0___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
lean_unreachable();
x_4 = lean::box(0);
lean::inc(x_4);
return x_4;
}
}
obj* l_fin_elim0(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
lean_unreachable();
x_4 = lean::box(0);
lean::inc(x_4);
return x_4;
}
}
obj* l_fin_of__nat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_0, x_2);
lean::dec(x_2);
lean::dec(x_0);
x_6 = lean::nat_mod(x_1, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_fin_add___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::nat_add(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::nat_mod(x_3, x_0);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
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
obj* l_fin_mul___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::nat_mul(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::nat_mod(x_3, x_0);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
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
obj* l_fin_sub___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::nat_sub(x_0, x_2);
lean::dec(x_2);
x_5 = lean::nat_add(x_1, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_8 = lean::nat_mod(x_5, x_0);
lean::dec(x_0);
lean::dec(x_5);
return x_8;
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
obj* l_fin_mod___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::nat_mod(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::nat_mod(x_3, x_0);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
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
obj* l_fin_div___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::nat_div(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::nat_mod(x_3, x_0);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
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
obj* l_fin_modn___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::nat_mod(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::nat_mod(x_3, x_0);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
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
obj* l_fin_has__zero(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::mk_nat_obj(0u);
return x_2;
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
obj* l_fin_has__add(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_add), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__sub(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_sub), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__mul(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_mul), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__mod(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_mod), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__div(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_div), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_fin_has__modn(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_modn), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
uint8 l_fin_decidable__eq___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (x_2 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* l_fin_decidable__eq(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_decidable__eq___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_fin_decidable__eq___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_fin_decidable__eq___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
void initialize_init_data_nat_div();
static bool _G_initialized = false;
void initialize_init_data_fin_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_div();
 l_fin_lt = _init_l_fin_lt();
 l_fin_le = _init_l_fin_le();
}

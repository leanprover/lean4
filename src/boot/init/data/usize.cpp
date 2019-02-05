// Lean compiler output
// Module: init.data.usize
// Imports: init.data.uint init.platform init.data.fin.default
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_nat_pow___main(obj*, obj*);
obj* l_usize_to__nat___boxed(obj*);
obj* l_usize_decidable__eq;
obj* l_usize_has__decidable__le___boxed(obj*, obj*);
obj* l_usize_has__mod;
obj* l_usize_dec__eq___boxed(obj*, obj*);
obj* l_usize_has__decidable__le(size_t, size_t);
obj* l_usize_inhabited___boxed;
obj* l_usize_sub___boxed(obj*, obj*);
obj* l_usize_div___boxed(obj*, obj*);
size_t l_usize_has__zero;
obj* l_usize_of__nat___boxed(obj*);
obj* l_usize_modn___boxed(obj*, obj*);
obj* l_usize_mod___boxed(obj*, obj*);
extern obj* l_system_platform_nbits;
obj* l_usize_has__decidable__lt(size_t, size_t);
obj* l_usize_has__mul;
obj* l_usize_add___boxed(obj*, obj*);
obj* l_usize_has__zero___boxed;
obj* l_usize_has__add;
obj* l_usize_has__modn;
obj* l_usize_lt;
obj* l_usize_has__le;
obj* l_usize_has__div;
obj* l_usize_has__lt;
obj* l_usize_dec__le___boxed(obj*, obj*);
obj* l_usize__sz;
obj* l_usize_has__sub;
obj* l_usize_le;
size_t l_usize_has__one;
obj* l_usize_has__one___boxed;
size_t l_usize_inhabited;
obj* l_usize_has__decidable__lt___boxed(obj*, obj*);
obj* l_usize_mul___boxed(obj*, obj*);
obj* l_usize_dec__lt___boxed(obj*, obj*);
obj* _init_l_usize__sz() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::mk_nat_obj(2u);
x_1 = l_system_platform_nbits;
lean::inc(x_1);
x_3 = l_nat_pow___main(x_0, x_1);
return x_3;
}
}
obj* l_usize_of__nat___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* l_usize_to__nat___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = lean::usize_to_nat(x_1);
return x_2;
}
}
obj* l_usize_add___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_add(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_sub(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_mul(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_div___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_div(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_mod(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_usize_modn___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::usize_modn(x_2, x_1);
x_4 = lean::box_size_t(x_3);
return x_4;
}
}
obj* _init_l_usize_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_usize_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
size_t _init_l_usize_has__zero() {
_start:
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_usize_has__zero___boxed() {
_start:
{
size_t x_0; obj* x_1; 
x_0 = l_usize_has__zero;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
size_t _init_l_usize_has__one() {
_start:
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_usize_has__one___boxed() {
_start:
{
size_t x_0; obj* x_1; 
x_0 = l_usize_has__one;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* _init_l_usize_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_sub___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_mul___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_mod___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__modn() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_modn___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_usize_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_usize_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
size_t _init_l_usize_inhabited() {
_start:
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_usize_inhabited___boxed() {
_start:
{
size_t x_0; obj* x_1; 
x_0 = l_usize_inhabited;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* l_usize_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_usize_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_dec_lt(x_2, x_3);
return x_4;
}
}
obj* l_usize_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_dec_le(x_2, x_3);
return x_4;
}
}
obj* _init_l_usize_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_usize_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_usize_has__decidable__lt(size_t x_0, size_t x_1) {
_start:
{
obj* x_2; 
x_2 = lean::usize_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_usize_has__decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_usize_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* l_usize_has__decidable__le(size_t x_0, size_t x_1) {
_start:
{
obj* x_2; 
x_2 = lean::usize_dec_le(x_0, x_1);
return x_2;
}
}
obj* l_usize_has__decidable__le___boxed(obj* x_0, obj* x_1) {
_start:
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = l_usize_has__decidable__le(x_2, x_3);
return x_4;
}
}
void initialize_init_data_uint();
void initialize_init_platform();
void initialize_init_data_fin_default();
static bool _G_initialized = false;
void initialize_init_data_usize() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_uint();
 initialize_init_platform();
 initialize_init_data_fin_default();
 l_usize__sz = _init_l_usize__sz();
 l_usize_lt = _init_l_usize_lt();
 l_usize_le = _init_l_usize_le();
 l_usize_has__zero = _init_l_usize_has__zero();
 l_usize_has__zero___boxed = _init_l_usize_has__zero___boxed();
 l_usize_has__one = _init_l_usize_has__one();
 l_usize_has__one___boxed = _init_l_usize_has__one___boxed();
 l_usize_has__add = _init_l_usize_has__add();
 l_usize_has__sub = _init_l_usize_has__sub();
 l_usize_has__mul = _init_l_usize_has__mul();
 l_usize_has__mod = _init_l_usize_has__mod();
 l_usize_has__modn = _init_l_usize_has__modn();
 l_usize_has__div = _init_l_usize_has__div();
 l_usize_has__lt = _init_l_usize_has__lt();
 l_usize_has__le = _init_l_usize_has__le();
 l_usize_inhabited = _init_l_usize_inhabited();
 l_usize_inhabited___boxed = _init_l_usize_inhabited___boxed();
 l_usize_decidable__eq = _init_l_usize_decidable__eq();
}

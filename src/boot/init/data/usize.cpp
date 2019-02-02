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
#endif
obj* _l_s3_nat_s3_pow_s6___main(obj*, obj*);
obj* _l_s5_usize_s7_to__nat_s7___boxed(obj*);
obj* _l_s5_usize_s13_decidable__eq;
obj* _l_s5_usize_s18_has__decidable__le_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s8_has__mod;
obj* _l_s5_usize_s7_dec__eq_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s18_has__decidable__le(size_t, size_t);
obj* _l_s5_usize_s9_inhabited_s7___boxed;
obj* _l_s5_usize_s3_sub_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_div_s7___boxed(obj*, obj*);
size_t _l_s5_usize_s9_has__zero;
obj* _l_s5_usize_s7_of__nat_s7___boxed(obj*);
obj* _l_s5_usize_s4_modn_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_mod_s7___boxed(obj*, obj*);
obj* _l_s6_system_s8_platform_s5_nbits;
obj* _l_s5_usize_s18_has__decidable__lt(size_t, size_t);
obj* _l_s5_usize_s8_has__mul;
obj* _l_s5_usize_s3_add_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s9_has__zero_s7___boxed;
obj* _l_s5_usize_s8_has__add;
obj* _l_s5_usize_s9_has__modn;
obj* _l_s5_usize_s2_lt;
obj* _l_s5_usize_s7_has__le;
obj* _l_s5_usize_s8_has__div;
obj* _l_s5_usize_s7_has__lt;
obj* _l_s5_usize_s7_dec__le_s7___boxed(obj*, obj*);
obj* _l_s9_usize__sz;
obj* _l_s5_usize_s8_has__sub;
obj* _l_s5_usize_s2_le;
size_t _l_s5_usize_s8_has__one;
obj* _l_s5_usize_s8_has__one_s7___boxed;
size_t _l_s5_usize_s9_inhabited;
obj* _l_s5_usize_s18_has__decidable__lt_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s3_mul_s7___boxed(obj*, obj*);
obj* _l_s5_usize_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _init__l_s9_usize__sz() {
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::mk_nat_obj(2u);
x_1 = _l_s6_system_s8_platform_s5_nbits;
lean::inc(x_1);
x_3 = _l_s3_nat_s3_pow_s6___main(x_0, x_1);
return x_3;
}
}
obj* _l_s5_usize_s7_of__nat_s7___boxed(obj* x_0) {
{
size_t x_1; obj* x_2; 
x_1 = lean::usize_of_nat(x_0);
x_2 = lean::box_size_t(x_1);
return x_2;
}
}
obj* _l_s5_usize_s7_to__nat_s7___boxed(obj* x_0) {
{
size_t x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = lean::usize_to_nat(x_1);
return x_2;
}
}
obj* _l_s5_usize_s3_add_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_add(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* _l_s5_usize_s3_sub_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_sub(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* _l_s5_usize_s3_mul_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_mul(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* _l_s5_usize_s3_div_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_div(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* _l_s5_usize_s3_mod_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; size_t x_4; obj* x_5; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_mod(x_2, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* _l_s5_usize_s4_modn_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::usize_modn(x_2, x_1);
x_4 = lean::box_size_t(x_3);
return x_4;
}
}
obj* _init__l_s5_usize_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_usize_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
size_t _init__l_s5_usize_s9_has__zero() {
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s5_usize_s9_has__zero_s7___boxed() {
{
size_t x_0; obj* x_1; 
x_0 = _l_s5_usize_s9_has__zero;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
size_t _init__l_s5_usize_s8_has__one() {
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s5_usize_s8_has__one_s7___boxed() {
{
size_t x_0; obj* x_1; 
x_0 = _l_s5_usize_s8_has__one;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* _init__l_s5_usize_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_add_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_sub_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_mul_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_mod_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s9_has__modn() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s4_modn_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s3_div_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_usize_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s5_usize_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
size_t _init__l_s5_usize_s9_inhabited() {
{
obj* x_0; size_t x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::usize_of_nat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s5_usize_s9_inhabited_s7___boxed() {
{
size_t x_0; obj* x_1; 
x_0 = _l_s5_usize_s9_inhabited;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
obj* _l_s5_usize_s7_dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_dec_eq(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_dec_lt(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::usize_dec_le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s5_usize_s13_decidable__eq() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_usize_s7_dec__eq_s7___boxed), 2, 0);
return x_0;
}
}
obj* _l_s5_usize_s18_has__decidable__lt(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = lean::usize_dec_lt(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s18_has__decidable__lt_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s18_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s5_usize_s18_has__decidable__le(size_t x_0, size_t x_1) {
{
obj* x_2; 
x_2 = lean::usize_dec_le(x_0, x_1);
return x_2;
}
}
obj* _l_s5_usize_s18_has__decidable__le_s7___boxed(obj* x_0, obj* x_1) {
{
size_t x_2; size_t x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_0);
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_usize_s18_has__decidable__le(x_2, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s4_uint();
void _l_initialize__l_s4_init_s8_platform();
void _l_initialize__l_s4_init_s4_data_s3_fin_s7_default();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s5_usize() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s4_uint();
 _l_initialize__l_s4_init_s8_platform();
 _l_initialize__l_s4_init_s4_data_s3_fin_s7_default();
 _l_s9_usize__sz = _init__l_s9_usize__sz();
 _l_s5_usize_s2_lt = _init__l_s5_usize_s2_lt();
 _l_s5_usize_s2_le = _init__l_s5_usize_s2_le();
 _l_s5_usize_s9_has__zero = _init__l_s5_usize_s9_has__zero();
 _l_s5_usize_s9_has__zero_s7___boxed = _init__l_s5_usize_s9_has__zero_s7___boxed();
 _l_s5_usize_s8_has__one = _init__l_s5_usize_s8_has__one();
 _l_s5_usize_s8_has__one_s7___boxed = _init__l_s5_usize_s8_has__one_s7___boxed();
 _l_s5_usize_s8_has__add = _init__l_s5_usize_s8_has__add();
 _l_s5_usize_s8_has__sub = _init__l_s5_usize_s8_has__sub();
 _l_s5_usize_s8_has__mul = _init__l_s5_usize_s8_has__mul();
 _l_s5_usize_s8_has__mod = _init__l_s5_usize_s8_has__mod();
 _l_s5_usize_s9_has__modn = _init__l_s5_usize_s9_has__modn();
 _l_s5_usize_s8_has__div = _init__l_s5_usize_s8_has__div();
 _l_s5_usize_s7_has__lt = _init__l_s5_usize_s7_has__lt();
 _l_s5_usize_s7_has__le = _init__l_s5_usize_s7_has__le();
 _l_s5_usize_s9_inhabited = _init__l_s5_usize_s9_inhabited();
 _l_s5_usize_s9_inhabited_s7___boxed = _init__l_s5_usize_s9_inhabited_s7___boxed();
 _l_s5_usize_s13_decidable__eq = _init__l_s5_usize_s13_decidable__eq();
}

// Lean compiler output
// Module: init.data.fin.basic
// Imports: init.data.nat.div
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s3_fin_s2_le;
obj* _l_s3_fin_s9_has__zero(obj*);
obj* _l_s3_fin_s5_elim0(obj*, obj*);
obj* _l_s3_fin_s7_dec__lt_s6___rarg(obj*, obj*);
obj* _l_s3_fin_s3_sub_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s9_has__modn(obj*);
obj* _l_s3_fin_s3_add_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s8_has__div(obj*);
obj* _l_s3_fin_s4_modn(obj*, obj*, obj*);
obj* _l_s3_fin_s3_add(obj*, obj*, obj*);
obj* _l_s3_fin_s13_decidable__eq(obj*);
obj* _l_s3_fin_s8_has__mul(obj*);
obj* _l_s3_fin_s8_has__mod(obj*);
obj* _l_s3_fin_s3_div(obj*, obj*, obj*);
obj* _l_s3_fin_s3_div_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s5_elim0_s6___main(obj*, obj*);
obj* _l_s3_fin_s7_of__nat(obj*, obj*);
obj* _l_s3_fin_s7_dec__lt(obj*);
obj* _l_s3_fin_s2_lt;
obj* _l_s3_fin_s4_modn_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s3_mul_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s8_has__add(obj*);
obj* _l_s3_fin_s3_mul(obj*, obj*, obj*);
obj* _l_s3_fin_s7_dec__le(obj*);
obj* _l_s3_fin_s13_decidable__eq_s6___rarg(obj*, obj*);
obj* _l_s3_fin_s7_dec__le_s6___rarg(obj*, obj*);
obj* _l_s3_fin_s7_has__le(obj*);
obj* _l_s3_fin_s7_has__lt(obj*);
obj* _l_s3_fin_s3_mod_s6___main(obj*, obj*, obj*);
obj* _l_s3_fin_s8_has__sub(obj*);
obj* _l_s3_fin_s3_sub(obj*, obj*, obj*);
obj* _l_s3_fin_s3_mod(obj*, obj*, obj*);
obj* _l_s3_fin_s8_has__one(obj*);
obj* _init__l_s3_fin_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_fin_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s3_fin_s7_has__lt(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
}
obj* _l_s3_fin_s7_has__le(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
}
obj* _l_s3_fin_s7_dec__lt_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _l_s3_fin_s7_dec__lt(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s7_dec__lt_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s3_fin_s7_dec__le_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _l_s3_fin_s7_dec__le(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s7_dec__le_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s3_fin_s5_elim0_s6___main(obj* x_0, obj* x_1) {
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
obj* _l_s3_fin_s5_elim0(obj* x_0, obj* x_1) {
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
obj* _l_s3_fin_s7_of__nat(obj* x_0, obj* x_1) {
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
obj* _l_s3_fin_s3_add_s6___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s3_fin_s3_add(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s3_fin_s3_add_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_fin_s3_mul_s6___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s3_fin_s3_mul(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s3_fin_s3_mul_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_fin_s3_sub_s6___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s3_fin_s3_sub(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s3_fin_s3_sub_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_fin_s3_mod_s6___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s3_fin_s3_mod(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s3_fin_s3_mod_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_fin_s3_div_s6___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s3_fin_s3_div(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s3_fin_s3_div_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_fin_s4_modn_s6___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s3_fin_s4_modn(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s3_fin_s4_modn_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s3_fin_s9_has__zero(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::mk_nat_obj(0u);
return x_2;
}
}
obj* _l_s3_fin_s8_has__one(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
return x_2;
}
}
obj* _l_s3_fin_s8_has__add(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s3_add), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s3_fin_s8_has__sub(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s3_sub), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s3_fin_s8_has__mul(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s3_mul), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s3_fin_s8_has__mod(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s3_mod), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s3_fin_s8_has__div(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s3_div), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s3_fin_s9_has__modn(obj* x_0) {
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s4_modn), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s3_fin_s13_decidable__eq_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _l_s3_fin_s13_decidable__eq(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s13_decidable__eq_s6___rarg), 2, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s3_fin_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
 _l_s3_fin_s2_lt = _init__l_s3_fin_s2_lt();
 _l_s3_fin_s2_le = _init__l_s3_fin_s2_le();
}

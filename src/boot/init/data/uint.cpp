// Lean compiler output
// Module: init.data.uint
// Imports: init.data.fin.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s5_uint8_s4_modn_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_has__le;
obj* _l_s6_uint32_s3_div_s6___main(unsigned, unsigned);
obj* _l_s6_uint16_s3_div(unsigned short, unsigned short);
obj* _l_s6_uint16_s3_mod_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint32_s3_mul_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s8_has__div;
obj* _l_s5_uint8_s7_to__nat(unsigned char);
obj* _l_s6_uint64_s3_sub_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_dec__le_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s9_inhabited;
obj* _l_s6_uint16_s3_sub_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s2_le;
obj* _l_s5_uint8_s7_dec__eq_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_mul_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s7_dec__le_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s18_has__decidable__lt(unsigned, unsigned);
obj* _l_s6_uint64_s7_dec__eq_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s7_dec__le(unsigned short, unsigned short);
obj* _l_s6_uint32_s7_dec__lt_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_dec__le_s6___main(unsigned, unsigned);
obj* _l_s5_uint8_s9_has__modn;
obj* _l_s6_uint32_s2_lt;
obj* _l_s6_uint64_s7_to__nat_s6___main_s7___boxed(obj*);
obj* _l_s6_uint16_s7_dec__eq(unsigned short, unsigned short);
obj* _l_s6_uint16_s18_has__decidable__lt(unsigned short, unsigned short);
obj* _l_s5_uint8_s13_decidable__eq;
obj* _l_s6_uint64_s3_mul_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s3_mul_s6___main_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s3_sub_s6___main(obj*, obj*, obj*);
obj* _l_s6_uint64_s8_has__one;
obj* _l_s6_uint32_s18_has__decidable__le(unsigned, unsigned);
obj* _l_s6_uint16_s3_mul_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s7_dec__le_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_div(unsigned char, unsigned char);
obj* _l_s5_uint8_s7_dec__lt(unsigned char, unsigned char);
obj* _l_s6_uint16_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _l_s9_uint8__sz;
obj* _l_s5_uint8_s3_sub_s6___main(unsigned char, unsigned char);
obj* _l_s6_uint64_s3_sub(unsigned long long, unsigned long long);
obj* _l_s5_uint8_s4_modn_s6___main(unsigned char, obj*);
obj* _l_s6_uint16_s2_le_s6___main;
obj* _l_s6_uint16_s7_has__lt;
obj* _l_s6_uint64_s7_has__lt;
obj* _l_s6_uint16_s8_has__mod;
obj* _l_s6_uint64_s13_decidable__eq;
obj* _l_s6_uint32_s3_mul(unsigned, unsigned);
obj* _l_s3_fin_s3_add_s6___main(obj*, obj*, obj*);
obj* _l_s6_uint16_s3_mod_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s8_has__add;
obj* _l_s5_uint8_s3_div_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s18_has__decidable__lt_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s7_to__nat(unsigned long long);
obj* _l_s5_uint8_s3_add_s6___main(unsigned char, unsigned char);
obj* _l_s5_uint8_s3_mod_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s3_sub_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint32_s7_to__nat(unsigned);
obj* _l_s6_uint16_s2_lt;
obj* _l_s10_uint32__sz;
obj* _l_s6_uint32_s7_dec__le_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s3_add_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s9_inhabited;
obj* _l_s5_uint8_s7_dec__lt_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s7_to__nat_s7___boxed(obj*);
obj* _l_s6_uint32_s7_dec__eq_s6___main(unsigned, unsigned);
obj* _l_s6_uint64_s3_mod_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s7_dec__lt_s6___main(unsigned long long, unsigned long long);
obj* _l_s6_uint64_s8_has__div;
obj* _l_s5_uint8_s7_dec__le(unsigned char, unsigned char);
obj* _l_s5_uint8_s3_add_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s8_has__div;
obj* _l_s6_uint32_s3_sub_s6___main(unsigned, unsigned);
obj* _l_s6_uint64_s8_has__sub;
obj* _l_s6_uint64_s8_has__mod;
obj* _l_s6_uint32_s3_div_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s7_dec__le_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint16_s3_mod_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s4_modn(unsigned long long, obj*);
obj* _l_s6_uint64_s3_add(unsigned long long, unsigned long long);
obj* _l_s6_uint16_s7_dec__le_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s18_has__decidable__le_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s18_has__decidable__le_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s3_div_s6___main(obj*, obj*, obj*);
obj* _l_s5_uint8_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_has__lt;
obj* _l_s6_uint32_s8_has__sub;
obj* _l_s6_uint16_s4_modn_s6___main(unsigned short, obj*);
obj* _l_s6_uint64_s3_mul_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s8_has__add;
obj* _l_s5_uint8_s4_modn(unsigned char, obj*);
obj* _l_s6_uint16_s7_dec__eq_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s9_has__modn;
obj* _l_s6_uint64_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s3_add_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_dec__eq_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s3_mul_s6___main(unsigned long long, unsigned long long);
obj* _l_s5_uint8_s3_mod(unsigned char, unsigned char);
obj* _l_s6_uint64_s3_add_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s4_modn_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s8_has__mul;
obj* _l_s6_uint64_s7_of__nat_s11___closed__1;
obj* _l_s5_uint8_s7_to__nat_s6___main_s7___boxed(obj*);
obj* _l_s6_uint32_s7_to__nat_s6___main(unsigned);
obj* _l_s6_uint64_s3_sub_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s7_of__nat(obj*);
obj* _l_s5_uint8_s18_has__decidable__le_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_mul_s6___main(unsigned char, unsigned char);
obj* _l_s6_uint16_s7_to__nat_s6___main(unsigned short);
obj* _l_s6_uint32_s3_mul_s6___main(unsigned, unsigned);
obj* _l_s6_uint64_s2_lt;
obj* _l_s6_uint64_s18_has__decidable__le(unsigned long long, unsigned long long);
obj* _l_s6_uint16_s3_add_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_mul(unsigned char, unsigned char);
obj* _l_s10_uint64__sz;
obj* _l_s6_uint32_s4_modn_s6___main(unsigned, obj*);
obj* _l_s5_uint8_s2_lt_s6___main;
obj* _l_s6_uint64_s3_mod_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_dec__eq_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s2_le;
obj* _l_s6_uint32_s3_mod_s6___main(unsigned, unsigned);
obj* _l_s6_uint64_s7_dec__le(unsigned long long, unsigned long long);
obj* _l_s5_uint8_s18_has__decidable__le(unsigned char, unsigned char);
obj* _l_s6_uint64_s7_dec__lt(unsigned long long, unsigned long long);
obj* _l_s6_uint16_s7_dec__eq_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_mod_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s2_lt;
obj* _l_s6_uint32_s4_modn_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s2_lt_s6___main;
obj* _l_s6_uint64_s3_div_s6___main(unsigned long long, unsigned long long);
obj* _l_s3_fin_s7_of__nat(obj*, obj*);
obj* _l_s6_uint64_s4_modn_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s3_mod_s6___main(unsigned long long, unsigned long long);
obj* _l_s6_uint32_s8_has__mod;
obj* _l_s5_uint8_s3_div_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s2_le_s6___main;
obj* _l_s6_uint32_s9_inhabited;
obj* _l_s6_uint32_s7_of__nat(obj*);
obj* _l_s6_uint32_s3_sub_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s8_has__div;
obj* _l_s3_fin_s4_modn_s6___main(obj*, obj*, obj*);
obj* _l_s6_uint16_s7_dec__lt_s6___main_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s3_mul_s6___main(obj*, obj*, obj*);
obj* _l_s5_uint8_s7_dec__le_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s18_has__decidable__lt_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s9_has__zero;
obj* _l_s6_uint64_s7_to__nat_s6___main(unsigned long long);
obj* _l_s6_uint16_s18_has__decidable__le(unsigned short, unsigned short);
obj* _l_s5_uint8_s7_dec__eq_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s4_modn(unsigned, obj*);
obj* _l_s6_uint16_s13_decidable__eq;
obj* _l_s5_uint8_s3_sub(unsigned char, unsigned char);
obj* _l_s5_uint8_s8_has__add;
obj* _l_s6_uint64_s3_div(unsigned long long, unsigned long long);
obj* _l_s5_uint8_s7_of__nat(obj*);
obj* _l_s6_uint32_s7_dec__eq(unsigned, unsigned);
obj* _l_s5_uint8_s3_mod_s6___main(unsigned char, unsigned char);
obj* _l_s6_uint32_s13_decidable__eq;
obj* _l_s6_uint32_s3_sub(unsigned, unsigned);
obj* _l_s6_uint16_s3_sub(unsigned short, unsigned short);
obj* _l_s6_uint64_s8_has__mul;
obj* _l_s6_uint64_s3_mul(unsigned long long, unsigned long long);
obj* _l_s6_uint16_s8_has__one;
obj* _l_s5_uint8_s3_sub_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s3_mul(unsigned short, unsigned short);
obj* _l_s5_uint8_s3_sub_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s7_dec__eq(unsigned long long, unsigned long long);
obj* _l_s6_uint64_s18_has__decidable__lt_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_add_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s3_sub_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s7_to__nat_s6___main_s7___boxed(obj*);
obj* _l_s6_uint16_s7_to__nat(unsigned short);
obj* _l_s6_uint16_s7_dec__eq_s6___main(unsigned short, unsigned short);
obj* _l_s10_uint16__sz;
obj* _l_s6_uint64_s3_add_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s8_has__one;
obj* _l_s6_uint32_s7_dec__lt_s6___main(unsigned, unsigned);
obj* _l_s6_uint64_s2_le;
obj* _l_s6_uint32_s3_div_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s3_mod(unsigned, unsigned);
obj* _l_s5_uint8_s3_mul_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s3_add(unsigned, unsigned);
obj* _l_s5_uint8_s7_dec__eq(unsigned char, unsigned char);
obj* _l_s5_uint8_s18_has__decidable__lt(unsigned char, unsigned char);
obj* _l_s6_uint64_s3_mod(unsigned long long, unsigned long long);
obj* _l_s6_uint32_s18_has__decidable__le_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s7_dec__le_s6___main(unsigned long long, unsigned long long);
obj* _l_s5_uint8_s8_has__mod;
obj* _l_s6_uint64_s7_has__le;
obj* _l_s5_uint8_s2_le;
obj* _l_s6_uint64_s3_div_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s3_mul_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint16_s3_div_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s7_has__lt;
obj* _l_s6_uint64_s18_has__decidable__lt(unsigned long long, unsigned long long);
obj* _l_s6_uint32_s2_lt_s6___main;
obj* _l_s5_uint8_s3_add(unsigned char, unsigned char);
obj* _l_s6_uint16_s9_has__modn;
obj* _l_s6_uint32_s3_mod_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s4_modn_s7___boxed(obj*, obj*);
obj* _l_s3_fin_s3_mod_s6___main(obj*, obj*, obj*);
obj* _l_s6_uint32_s7_dec__lt_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s3_div_s6___main(unsigned char, unsigned char);
obj* _l_s6_uint64_s7_dec__lt_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s3_add_s6___main(unsigned, unsigned);
obj* _l_s6_uint16_s7_of__nat(obj*);
obj* _l_s5_uint8_s7_has__le;
obj* _l_s6_uint16_s7_dec__lt_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint64_s4_modn_s6___main(unsigned long long, obj*);
obj* _l_s6_uint64_s7_dec__le_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s4_modn_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s3_sub_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s7_has__le;
obj* _l_s5_uint8_s7_to__nat_s7___boxed(obj*);
obj* _l_s5_uint8_s8_has__mul;
obj* _l_s6_uint16_s7_to__nat_s6___main_s7___boxed(obj*);
obj* _l_s6_uint64_s3_add_s6___main(unsigned long long, unsigned long long);
obj* _l_s6_uint16_s18_has__decidable__lt_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s2_lt_s6___main;
obj* _l_s6_uint16_s4_modn(unsigned short, obj*);
obj* _l_s5_uint8_s7_dec__lt_s6___main(unsigned char, unsigned char);
obj* _l_s6_uint32_s3_mod_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s9_has__modn;
obj* _l_s5_uint8_s8_has__sub;
obj* _l_s6_uint32_s7_dec__lt(unsigned, unsigned);
obj* _l_s5_uint8_s7_dec__eq_s6___main(unsigned char, unsigned char);
obj* _l_s6_uint32_s7_to__nat_s7___boxed(obj*);
obj* _l_s6_uint32_s8_has__one;
obj* _l_s6_uint32_s3_mul_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s3_sub_s6___main(unsigned long long, unsigned long long);
obj* _l_s6_uint64_s7_dec__le_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s8_has__sub;
obj* _l_s6_uint16_s3_mod(unsigned short, unsigned short);
obj* _l_s6_uint16_s3_add_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint64_s2_le_s6___main;
obj* _l_s5_uint8_s4_modn_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s7_dec__lt(unsigned short, unsigned short);
obj* _l_s6_uint64_s7_to__nat_s7___boxed(obj*);
obj* _l_s6_uint16_s3_div_s6___main(unsigned short, unsigned short);
obj* _l_s6_uint16_s3_add_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s9_has__zero;
obj* _l_s6_uint64_s7_dec__eq_s7___boxed(obj*, obj*);
obj* _l_s6_uint16_s3_add(unsigned short, unsigned short);
obj* _l_s6_uint16_s4_modn_s6___main_s7___boxed(obj*, obj*);
obj* _l_s5_uint8_s7_to__nat_s6___main(unsigned char);
obj* _l_s6_uint32_s9_has__zero;
obj* _l_s6_uint16_s9_inhabited;
obj* _l_s6_uint32_s8_has__mul;
obj* _l_s6_uint64_s9_has__zero;
obj* _l_s6_uint32_s3_div(unsigned, unsigned);
obj* _l_s5_uint8_s2_le_s6___main;
obj* _l_s6_uint32_s7_dec__le(unsigned, unsigned);
obj* _l_s6_uint64_s3_div_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint64_s7_dec__eq_s6___main(unsigned long long, unsigned long long);
obj* _l_s6_uint16_s3_div_s6___main_s7___boxed(obj*, obj*);
obj* _l_s6_uint32_s8_has__add;
obj* _l_s5_uint8_s7_dec__le_s6___main(unsigned char, unsigned char);
obj* _init__l_s9_uint8__sz() {
{
obj* x_0; 
x_0 = lean::mk_nat_obj(65536u);
return x_0;
}
}
obj* _l_s5_uint8_s7_of__nat(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(65535u);
x_2 = _l_s3_fin_s7_of__nat(x_1, x_0);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s5_uint8_s7_to__nat_s6___main(unsigned char x_0) {
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s5_uint8_s7_to__nat_s6___main_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s5_uint8_s7_to__nat_s6___main(x_1);
return x_2;
}
}
obj* _l_s5_uint8_s7_to__nat(unsigned char x_0) {
{
obj* x_1; 
x_1 = _l_s5_uint8_s7_to__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s5_uint8_s7_to__nat_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s5_uint8_s7_to__nat(x_1);
return x_2;
}
}
obj* _l_s5_uint8_s3_add_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_uint8__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_add_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_uint8_s3_add_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_add_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_add(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s3_add_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s3_add_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_add(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_sub_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_uint8__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_sub_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_uint8_s3_sub_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_sub_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_sub(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s3_sub_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s3_sub_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_sub(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_mul_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_uint8__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mul_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_uint8_s3_mul_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_mul_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_mul(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s3_mul_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s3_mul_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_mul(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_div_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_uint8__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_div_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_uint8_s3_div_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_div_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_div(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s3_div_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s3_div_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_div(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_mod_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s9_uint8__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mod_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s5_uint8_s3_mod_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_mod_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s3_mod(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s3_mod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s3_mod_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s3_mod(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s4_modn_s6___main(unsigned char x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = _l_s9_uint8__sz;
lean::inc(x_5);
x_7 = _l_s3_fin_s4_modn_s6___main(x_5, x_2, x_1);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _l_s5_uint8_s4_modn_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = _l_s5_uint8_s4_modn_s6___main(x_2, x_1);
return x_3;
}
}
obj* _l_s5_uint8_s4_modn(unsigned char x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s4_modn_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s4_modn_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = _l_s5_uint8_s4_modn(x_2, x_1);
return x_3;
}
}
obj* _init__l_s5_uint8_s2_lt_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_uint8_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_uint8_s2_le_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_uint8_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s5_uint8_s9_has__zero() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(65535u);
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s5_uint8_s8_has__one() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(65535u);
x_1 = lean::mk_nat_obj(1u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s5_uint8_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s3_add_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_uint8_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s3_sub_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_uint8_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s3_mul_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_uint8_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s3_mod_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_uint8_s9_has__modn() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s4_modn_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_uint8_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s3_div_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s5_uint8_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s5_uint8_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s5_uint8_s9_inhabited() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(65535u);
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s5_uint8_s7_dec__eq_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_eq(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s5_uint8_s7_dec__eq_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s7_dec__eq_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s7_dec__eq(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s7_dec__eq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s7_dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s7_dec__eq(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s7_dec__lt_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s5_uint8_s7_dec__lt_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s7_dec__lt_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s7_dec__lt(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s7_dec__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s7_dec__le_s6___main(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_le(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s5_uint8_s7_dec__le_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s7_dec__le_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s7_dec__le(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s7_dec__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s5_uint8_s13_decidable__eq() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_uint8_s7_dec__eq_s7___boxed), 2, 0);
return x_0;
}
}
obj* _l_s5_uint8_s18_has__decidable__lt(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s18_has__decidable__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s18_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s5_uint8_s18_has__decidable__le(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s5_uint8_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s5_uint8_s18_has__decidable__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s5_uint8_s18_has__decidable__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s10_uint16__sz() {
{
obj* x_0; 
x_0 = lean::mk_nat_obj(65536u);
return x_0;
}
}
obj* _l_s6_uint16_s7_of__nat(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(65535u);
x_2 = _l_s3_fin_s7_of__nat(x_1, x_0);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s6_uint16_s7_to__nat_s6___main(unsigned short x_0) {
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s6_uint16_s7_to__nat_s6___main_s7___boxed(obj* x_0) {
{
unsigned short x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s6_uint16_s7_to__nat_s6___main(x_1);
return x_2;
}
}
obj* _l_s6_uint16_s7_to__nat(unsigned short x_0) {
{
obj* x_1; 
x_1 = _l_s6_uint16_s7_to__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s6_uint16_s7_to__nat_s7___boxed(obj* x_0) {
{
unsigned short x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s6_uint16_s7_to__nat(x_1);
return x_2;
}
}
obj* _l_s6_uint16_s3_add_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint16__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_add_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint16_s3_add_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_add_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_add(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s3_add_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s3_add_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_add(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_sub_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint16__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_sub_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint16_s3_sub_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_sub_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_sub(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s3_sub_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s3_sub_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_sub(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_mul_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint16__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mul_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint16_s3_mul_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_mul_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_mul(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s3_mul_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s3_mul_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_mul(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_div_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint16__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_div_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint16_s3_div_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_div_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_div(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s3_div_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s3_div_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_div(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_mod_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint16__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mod_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint16_s3_mod_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_mod_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s3_mod(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s3_mod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s3_mod_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s3_mod(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s4_modn_s6___main(unsigned short x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = _l_s10_uint16__sz;
lean::inc(x_5);
x_7 = _l_s3_fin_s4_modn_s6___main(x_5, x_2, x_1);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _l_s6_uint16_s4_modn_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = _l_s6_uint16_s4_modn_s6___main(x_2, x_1);
return x_3;
}
}
obj* _l_s6_uint16_s4_modn(unsigned short x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s4_modn_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s4_modn_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = _l_s6_uint16_s4_modn(x_2, x_1);
return x_3;
}
}
obj* _init__l_s6_uint16_s2_lt_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint16_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint16_s2_le_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint16_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint16_s9_has__zero() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(65535u);
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s6_uint16_s8_has__one() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(65535u);
x_1 = lean::mk_nat_obj(1u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s6_uint16_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s3_add_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint16_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s3_sub_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint16_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s3_mul_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint16_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s3_mod_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint16_s9_has__modn() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s4_modn_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint16_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s3_div_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint16_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s6_uint16_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s6_uint16_s9_inhabited() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(65535u);
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s6_uint16_s7_dec__eq_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_eq(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint16_s7_dec__eq_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s7_dec__eq_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s7_dec__eq(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s7_dec__eq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s7_dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s7_dec__eq(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s7_dec__lt_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint16_s7_dec__lt_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s7_dec__lt_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s7_dec__lt(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s7_dec__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s7_dec__le_s6___main(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_le(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint16_s7_dec__le_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s7_dec__le_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s7_dec__le(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s7_dec__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s6_uint16_s13_decidable__eq() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint16_s7_dec__eq_s7___boxed), 2, 0);
return x_0;
}
}
obj* _l_s6_uint16_s18_has__decidable__lt(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s18_has__decidable__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s18_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint16_s18_has__decidable__le(unsigned short x_0, unsigned short x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint16_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint16_s18_has__decidable__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned short x_2; unsigned short x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s6_uint16_s18_has__decidable__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s10_uint32__sz() {
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967296"));
return x_0;
}
}
obj* _l_s6_uint32_s7_of__nat(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(lean::mpz("4294967295"));
x_2 = _l_s3_fin_s7_of__nat(x_1, x_0);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s6_uint32_s7_to__nat_s6___main(unsigned x_0) {
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s6_uint32_s7_to__nat_s6___main_s7___boxed(obj* x_0) {
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s6_uint32_s7_to__nat_s6___main(x_1);
return x_2;
}
}
obj* _l_s6_uint32_s7_to__nat(unsigned x_0) {
{
obj* x_1; 
x_1 = _l_s6_uint32_s7_to__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s6_uint32_s7_to__nat_s7___boxed(obj* x_0) {
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s6_uint32_s7_to__nat(x_1);
return x_2;
}
}
obj* _l_s6_uint32_s3_add_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint32__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_add_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint32_s3_add_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_add_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_add(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s3_add_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s3_add_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_add(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_sub_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint32__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_sub_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint32_s3_sub_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_sub_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_sub(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s3_sub_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s3_sub_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_sub(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_mul_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint32__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mul_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint32_s3_mul_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_mul_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_mul(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s3_mul_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s3_mul_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_mul(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_div_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint32__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_div_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint32_s3_div_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_div_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_div(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s3_div_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s3_div_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_div(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_mod_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint32__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mod_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint32_s3_mod_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_mod_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s3_mod(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s3_mod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s3_mod_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s3_mod(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s4_modn_s6___main(unsigned x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = _l_s10_uint32__sz;
lean::inc(x_5);
x_7 = _l_s3_fin_s4_modn_s6___main(x_5, x_2, x_1);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _l_s6_uint32_s4_modn_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = _l_s6_uint32_s4_modn_s6___main(x_2, x_1);
return x_3;
}
}
obj* _l_s6_uint32_s4_modn(unsigned x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s4_modn_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s4_modn_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = _l_s6_uint32_s4_modn(x_2, x_1);
return x_3;
}
}
obj* _init__l_s6_uint32_s2_lt_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint32_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint32_s2_le_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint32_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint32_s9_has__zero() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967295"));
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s6_uint32_s8_has__one() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967295"));
x_1 = lean::mk_nat_obj(1u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s6_uint32_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s3_add_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint32_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s3_sub_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint32_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s3_mul_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint32_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s3_mod_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint32_s9_has__modn() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s4_modn_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint32_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s3_div_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint32_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s6_uint32_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s6_uint32_s9_inhabited() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(lean::mpz("4294967295"));
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s6_uint32_s7_dec__eq_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_eq(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint32_s7_dec__eq_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s7_dec__eq_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s7_dec__eq(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s7_dec__eq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s7_dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s7_dec__eq(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s7_dec__lt_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint32_s7_dec__lt_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s7_dec__lt_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s7_dec__lt(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s7_dec__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s7_dec__le_s6___main(unsigned x_0, unsigned x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_le(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint32_s7_dec__le_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s7_dec__le_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s7_dec__le(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s7_dec__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s6_uint32_s13_decidable__eq() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint32_s7_dec__eq_s7___boxed), 2, 0);
return x_0;
}
}
obj* _l_s6_uint32_s18_has__decidable__lt(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s18_has__decidable__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s18_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint32_s18_has__decidable__le(unsigned x_0, unsigned x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint32_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint32_s18_has__decidable__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; unsigned x_3; obj* x_4; 
x_2 = lean::unbox_uint32(x_0);
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s6_uint32_s18_has__decidable__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s10_uint64__sz() {
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551616"));
return x_0;
}
}
obj* _l_s6_uint64_s7_of__nat(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = _l_s6_uint64_s7_of__nat_s11___closed__1;
lean::inc(x_1);
x_3 = _l_s3_fin_s7_of__nat(x_1, x_0);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* _init__l_s6_uint64_s7_of__nat_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551615"));
return x_0;
}
}
obj* _l_s6_uint64_s7_to__nat_s6___main(unsigned long long x_0) {
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s6_uint64_s7_to__nat_s6___main_s7___boxed(obj* x_0) {
{
unsigned long long x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = _l_s6_uint64_s7_to__nat_s6___main(x_1);
return x_2;
}
}
obj* _l_s6_uint64_s7_to__nat(unsigned long long x_0) {
{
obj* x_1; 
x_1 = _l_s6_uint64_s7_to__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s6_uint64_s7_to__nat_s7___boxed(obj* x_0) {
{
unsigned long long x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = _l_s6_uint64_s7_to__nat(x_1);
return x_2;
}
}
obj* _l_s6_uint64_s3_add_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint64__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_add_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint64_s3_add_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_add_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_add(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s3_add_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s3_add_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_add(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_sub_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint64__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_sub_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint64_s3_sub_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_sub_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_sub(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s3_sub_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s3_sub_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_sub(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_mul_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint64__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mul_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint64_s3_mul_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_mul_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_mul(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s3_mul_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s3_mul_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_mul(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_div_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint64__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_div_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint64_s3_div_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_div_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_div(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s3_div_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s3_div_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_div(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_mod_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = _l_s10_uint64__sz;
lean::inc(x_8);
x_10 = _l_s3_fin_s3_mod_s6___main(x_8, x_2, x_5);
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* _l_s6_uint64_s3_mod_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_mod_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s3_mod(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s3_mod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s3_mod_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s3_mod(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s4_modn_s6___main(unsigned long long x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = _l_s10_uint64__sz;
lean::inc(x_5);
x_7 = _l_s3_fin_s4_modn_s6___main(x_5, x_2, x_1);
if (lean::is_scalar(x_4)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_4;
}
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _l_s6_uint64_s4_modn_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; obj* x_3; 
x_2 = lean::unbox_uint64(x_0);
x_3 = _l_s6_uint64_s4_modn_s6___main(x_2, x_1);
return x_3;
}
}
obj* _l_s6_uint64_s4_modn(unsigned long long x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s4_modn_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s4_modn_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; obj* x_3; 
x_2 = lean::unbox_uint64(x_0);
x_3 = _l_s6_uint64_s4_modn(x_2, x_1);
return x_3;
}
}
obj* _init__l_s6_uint64_s2_lt_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint64_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint64_s2_le_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint64_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s6_uint64_s9_has__zero() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551615"));
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s6_uint64_s8_has__one() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551615"));
x_1 = lean::mk_nat_obj(1u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init__l_s6_uint64_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s3_add_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint64_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s3_sub_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint64_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s3_mul_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint64_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s3_mod_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint64_s9_has__modn() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s4_modn_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint64_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s3_div_s7___boxed), 2, 0);
return x_0;
}
}
obj* _init__l_s6_uint64_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s6_uint64_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s6_uint64_s9_inhabited() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::mk_nat_obj(lean::mpz("18446744073709551615"));
x_1 = lean::mk_nat_obj(0u);
x_2 = _l_s3_fin_s7_of__nat(x_0, x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _l_s6_uint64_s7_dec__eq_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_eq(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint64_s7_dec__eq_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s7_dec__eq_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s7_dec__eq(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s7_dec__eq_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s7_dec__eq_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s7_dec__eq(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s7_dec__lt_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint64_s7_dec__lt_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s7_dec__lt_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s7_dec__lt(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s7_dec__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s7_dec__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s7_dec__le_s6___main(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; obj* x_5; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::nat_dec_le(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_8;
}
}
obj* _l_s6_uint64_s7_dec__le_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s7_dec__le_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s7_dec__le(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s7_dec__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s7_dec__le(x_2, x_3);
return x_4;
}
}
obj* _init__l_s6_uint64_s13_decidable__eq() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_uint64_s7_dec__eq_s7___boxed), 2, 0);
return x_0;
}
}
obj* _l_s6_uint64_s18_has__decidable__lt(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s7_dec__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s18_has__decidable__lt_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s18_has__decidable__lt(x_2, x_3);
return x_4;
}
}
obj* _l_s6_uint64_s18_has__decidable__le(unsigned long long x_0, unsigned long long x_1) {
{
obj* x_2; 
x_2 = _l_s6_uint64_s7_dec__le_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s6_uint64_s18_has__decidable__le_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned long long x_2; unsigned long long x_3; obj* x_4; 
x_2 = lean::unbox_uint64(x_0);
x_3 = lean::unbox_uint64(x_1);
x_4 = _l_s6_uint64_s18_has__decidable__le(x_2, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s3_fin_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s4_uint() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_fin_s5_basic();
 _l_s9_uint8__sz = _init__l_s9_uint8__sz();
 _l_s5_uint8_s2_lt_s6___main = _init__l_s5_uint8_s2_lt_s6___main();
 _l_s5_uint8_s2_lt = _init__l_s5_uint8_s2_lt();
 _l_s5_uint8_s2_le_s6___main = _init__l_s5_uint8_s2_le_s6___main();
 _l_s5_uint8_s2_le = _init__l_s5_uint8_s2_le();
 _l_s5_uint8_s9_has__zero = _init__l_s5_uint8_s9_has__zero();
 _l_s5_uint8_s8_has__one = _init__l_s5_uint8_s8_has__one();
 _l_s5_uint8_s8_has__add = _init__l_s5_uint8_s8_has__add();
 _l_s5_uint8_s8_has__sub = _init__l_s5_uint8_s8_has__sub();
 _l_s5_uint8_s8_has__mul = _init__l_s5_uint8_s8_has__mul();
 _l_s5_uint8_s8_has__mod = _init__l_s5_uint8_s8_has__mod();
 _l_s5_uint8_s9_has__modn = _init__l_s5_uint8_s9_has__modn();
 _l_s5_uint8_s8_has__div = _init__l_s5_uint8_s8_has__div();
 _l_s5_uint8_s7_has__lt = _init__l_s5_uint8_s7_has__lt();
 _l_s5_uint8_s7_has__le = _init__l_s5_uint8_s7_has__le();
 _l_s5_uint8_s9_inhabited = _init__l_s5_uint8_s9_inhabited();
 _l_s5_uint8_s13_decidable__eq = _init__l_s5_uint8_s13_decidable__eq();
 _l_s10_uint16__sz = _init__l_s10_uint16__sz();
 _l_s6_uint16_s2_lt_s6___main = _init__l_s6_uint16_s2_lt_s6___main();
 _l_s6_uint16_s2_lt = _init__l_s6_uint16_s2_lt();
 _l_s6_uint16_s2_le_s6___main = _init__l_s6_uint16_s2_le_s6___main();
 _l_s6_uint16_s2_le = _init__l_s6_uint16_s2_le();
 _l_s6_uint16_s9_has__zero = _init__l_s6_uint16_s9_has__zero();
 _l_s6_uint16_s8_has__one = _init__l_s6_uint16_s8_has__one();
 _l_s6_uint16_s8_has__add = _init__l_s6_uint16_s8_has__add();
 _l_s6_uint16_s8_has__sub = _init__l_s6_uint16_s8_has__sub();
 _l_s6_uint16_s8_has__mul = _init__l_s6_uint16_s8_has__mul();
 _l_s6_uint16_s8_has__mod = _init__l_s6_uint16_s8_has__mod();
 _l_s6_uint16_s9_has__modn = _init__l_s6_uint16_s9_has__modn();
 _l_s6_uint16_s8_has__div = _init__l_s6_uint16_s8_has__div();
 _l_s6_uint16_s7_has__lt = _init__l_s6_uint16_s7_has__lt();
 _l_s6_uint16_s7_has__le = _init__l_s6_uint16_s7_has__le();
 _l_s6_uint16_s9_inhabited = _init__l_s6_uint16_s9_inhabited();
 _l_s6_uint16_s13_decidable__eq = _init__l_s6_uint16_s13_decidable__eq();
 _l_s10_uint32__sz = _init__l_s10_uint32__sz();
 _l_s6_uint32_s2_lt_s6___main = _init__l_s6_uint32_s2_lt_s6___main();
 _l_s6_uint32_s2_lt = _init__l_s6_uint32_s2_lt();
 _l_s6_uint32_s2_le_s6___main = _init__l_s6_uint32_s2_le_s6___main();
 _l_s6_uint32_s2_le = _init__l_s6_uint32_s2_le();
 _l_s6_uint32_s9_has__zero = _init__l_s6_uint32_s9_has__zero();
 _l_s6_uint32_s8_has__one = _init__l_s6_uint32_s8_has__one();
 _l_s6_uint32_s8_has__add = _init__l_s6_uint32_s8_has__add();
 _l_s6_uint32_s8_has__sub = _init__l_s6_uint32_s8_has__sub();
 _l_s6_uint32_s8_has__mul = _init__l_s6_uint32_s8_has__mul();
 _l_s6_uint32_s8_has__mod = _init__l_s6_uint32_s8_has__mod();
 _l_s6_uint32_s9_has__modn = _init__l_s6_uint32_s9_has__modn();
 _l_s6_uint32_s8_has__div = _init__l_s6_uint32_s8_has__div();
 _l_s6_uint32_s7_has__lt = _init__l_s6_uint32_s7_has__lt();
 _l_s6_uint32_s7_has__le = _init__l_s6_uint32_s7_has__le();
 _l_s6_uint32_s9_inhabited = _init__l_s6_uint32_s9_inhabited();
 _l_s6_uint32_s13_decidable__eq = _init__l_s6_uint32_s13_decidable__eq();
 _l_s10_uint64__sz = _init__l_s10_uint64__sz();
 _l_s6_uint64_s7_of__nat_s11___closed__1 = _init__l_s6_uint64_s7_of__nat_s11___closed__1();
 _l_s6_uint64_s2_lt_s6___main = _init__l_s6_uint64_s2_lt_s6___main();
 _l_s6_uint64_s2_lt = _init__l_s6_uint64_s2_lt();
 _l_s6_uint64_s2_le_s6___main = _init__l_s6_uint64_s2_le_s6___main();
 _l_s6_uint64_s2_le = _init__l_s6_uint64_s2_le();
 _l_s6_uint64_s9_has__zero = _init__l_s6_uint64_s9_has__zero();
 _l_s6_uint64_s8_has__one = _init__l_s6_uint64_s8_has__one();
 _l_s6_uint64_s8_has__add = _init__l_s6_uint64_s8_has__add();
 _l_s6_uint64_s8_has__sub = _init__l_s6_uint64_s8_has__sub();
 _l_s6_uint64_s8_has__mul = _init__l_s6_uint64_s8_has__mul();
 _l_s6_uint64_s8_has__mod = _init__l_s6_uint64_s8_has__mod();
 _l_s6_uint64_s9_has__modn = _init__l_s6_uint64_s9_has__modn();
 _l_s6_uint64_s8_has__div = _init__l_s6_uint64_s8_has__div();
 _l_s6_uint64_s7_has__lt = _init__l_s6_uint64_s7_has__lt();
 _l_s6_uint64_s7_has__le = _init__l_s6_uint64_s7_has__le();
 _l_s6_uint64_s9_inhabited = _init__l_s6_uint64_s9_inhabited();
 _l_s6_uint64_s13_decidable__eq = _init__l_s6_uint64_s13_decidable__eq();
}

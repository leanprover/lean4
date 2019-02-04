// Lean compiler output
// Module: init.data.repr
// Imports: init.data.string.basic init.data.uint init.data.usize init.data.nat.div
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s3_nat_s11_digit__char_s11___closed__2;
obj* _l_s3_nat_s11_digit__char_s12___closed__38;
obj* _l_s5_sigma_s9_has__repr(obj*, obj*);
obj* _l_s6_uint64_s9_has__repr(unsigned long long);
obj* _l_s4_unit_s9_has__repr_s7___boxed(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__37;
obj* _l_s3_nat_s11_digit__char_s12___closed__21;
obj* _l_s4_char_s9_has__repr(unsigned);
obj* _l_s4_list_s9_has__repr_s6___rarg(obj*);
obj* _l_s3_nat_s9_has__repr;
obj* _l_s3_nat_s11_digit__char_s12___closed__14;
obj* _l_s4_prod_s9_has__repr_s6___rarg(obj*, obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__46;
obj* _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s3_nat_s11_digit__succ(obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__30;
obj* _l_s4_unit_s9_has__repr_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__10;
obj* _l_s7_subtype_s9_has__repr_s6___rarg(obj*, obj*);
obj* _l_s2_id_s9_has__repr_s6___rarg(obj*);
obj* _l_s4_bool_s9_has__repr(unsigned char);
obj* _l_s4_unit_s9_has__repr(unsigned char);
obj* _l_s4_list_s3_map_s6___main_s4___at_s3_nat_s4_repr_s9___spec__1(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__51;
obj* _l_s4_char_s11_quote__core_s11___closed__5;
obj* _l_s3_nat_s10_to__digits_s6___main_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__13;
obj* _l_s3_nat_s11_digit__char_s12___closed__23;
obj* _l_s9_decidable_s9_has__repr(obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2;
obj* _l_s4_char_s11_quote__core_s11___closed__1;
obj* _l_s6_uint32_s9_has__repr_s7___boxed(obj*);
obj* _l_s3_nat_s11_digit__succ_s6___main(obj*, obj*);
obj* _l_s4_char_s11_quote__core(unsigned);
obj* _l_s6_string_s9_has__repr;
obj* _l_s3_fin_s9_has__repr_s6___rarg(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__33;
obj* _l_s4_prod_s9_has__repr(obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__17;
obj* _l_s3_nat_s11_digit__char_s11___closed__4;
obj* _l_s3_nat_s11_digit__char_s12___closed__42;
obj* _l_s6_string_s5_quote_s11___closed__2;
obj* _l_s3_nat_s11_digit__char_s12___closed__47;
obj* _l_s3_nat_s11_digit__char_s11___closed__3;
obj* _l_s3_nat_s11_digit__char_s12___closed__40;
obj* _l_s3_nat_s11_digit__char_s12___closed__16;
obj* _l_s13_char__to__hex(unsigned);
obj* _l_s3_nat_s11_digit__char_s11___closed__1;
obj* _l_s3_sum_s9_has__repr(obj*, obj*);
obj* _l_s5_usize_s9_has__repr(size_t);
obj* _l_s4_char_s4_repr_s7___boxed(obj*);
obj* _l_s7_subtype_s9_has__repr(obj*, obj*);
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__27;
obj* _l_s6_option_s9_has__repr(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__43;
obj* _l_s3_nat_s11_digit__char_s12___closed__18;
obj* _l_s4_list_s9_has__repr(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__29;
obj* _l_s3_nat_s11_digit__char_s12___closed__34;
obj* _l_s3_nat_s11_digit__char_s11___closed__8;
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__45;
obj* _l_s2_id_s9_has__repr(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__31;
obj* _l_s4_list_s4_repr_s6___main(obj*);
obj* _l_s16_hex__digit__repr(obj*);
obj* _l_s5_usize_s9_has__repr_s7___boxed(obj*);
obj* _l_s4_char_s11_quote__core_s11___closed__3;
obj* _l_s3_fin_s9_has__repr(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__39;
obj* _l_s3_nat_s11_digit__char_s12___closed__36;
obj* _l_s4_char_s9_has__repr_s11___closed__1;
obj* _l_s6_string_s8_iterator_s9_has__repr(obj*);
obj* _l_s6_uint16_s9_has__repr(unsigned short);
obj* _l_s3_nat_s11_digit__char_s12___closed__28;
obj* _l_s6_uint16_s9_has__repr_s7___boxed(obj*);
obj* _l_s6_uint64_s9_has__repr_s7___boxed(obj*);
obj* _l_s3_nat_s11_digit__char_s11___closed__5;
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
unsigned char _l_s6_string_s9_is__empty(obj*);
obj* _l_s3_nat_s11_digit__char(obj*);
obj* _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__2;
obj* _l_s4_bool_s9_has__repr_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__48;
obj* _l_s3_nat_s11_digit__char_s12___closed__24;
obj* _l_s4_list_s7_reverse_s6___rarg(obj*);
obj* _l_s4_list_s9_repr__aux_s6___rarg(obj*, unsigned char, obj*);
extern obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s11___closed__7;
obj* _l_s4_list_s4_repr(obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__44;
obj* _l_s4_list_s4_repr_s6___rarg(obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__50;
obj* _l_s3_nat_s11_digit__char_s12___closed__41;
obj* _l_s6_string_s5_quote_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__35;
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__1;
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__2;
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s6_string_s10_quote__aux_s6___main(obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
obj* _l_s3_nat_s11_digit__char_s12___closed__26;
obj* _l_s3_nat_s11_digit__char_s12___closed__32;
obj* _l_s4_bool_s9_has__repr_s11___closed__2;
obj* _l_s9_decidable_s9_has__repr_s6___rarg(obj*);
obj* _l_s6_option_s9_has__repr_s6___rarg(obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s11___closed__9;
obj* _l_s4_char_s11_quote__core_s7___boxed(obj*);
obj* _l_s3_nat_s10_to__digits(obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__25;
obj* _l_s13_char__to__hex_s7___boxed(obj*);
obj* _l_s4_char_s4_repr(unsigned);
obj* _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__2;
obj* _l_s4_list_s9_repr__aux(obj*);
obj* _l_s4_char_s9_has__repr_s7___boxed(obj*);
obj* _l_s3_sum_s9_has__repr_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s9_repr__aux_s6___main(obj*);
obj* _l_s4_list_s9_repr__aux_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__20;
obj* _l_s4_char_s11_quote__core_s11___closed__4;
obj* _l_s3_nat_s11_digit__char_s11___closed__6;
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s6_string_s8_iterator_s9_has__repr_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__15;
obj* _l_s3_nat_s11_digit__char_s12___closed__49;
obj* _l_s5_sigma_s9_has__repr_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg(obj*, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__22;
obj* _l_s6_string_s10_quote__aux(obj*);
obj* _l_s6_string_s5_quote(obj*);
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg(obj*, unsigned char, obj*);
obj* _l_s3_nat_s11_digit__char_s12___closed__19;
obj* _l_s6_uint32_s9_has__repr(unsigned);
obj* _l_s4_bool_s9_has__repr_s7___boxed(obj*);
obj* _l_s3_nat_s10_to__digits_s6___main(obj*, obj*);
obj* _l_s4_char_s11_quote__core_s11___closed__2;
obj* _l_s3_nat_s11_digit__char_s12___closed__12;
obj* _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s3_nat_s11_digit__char_s12___closed__11;
obj* _l_s2_id_s9_has__repr_s6___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* _l_s2_id_s9_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s9_has__repr_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_bool_s9_has__repr(unsigned char x_0) {
_start:
{
if (x_0 == 0)
{
obj* x_1; 
x_1 = _l_s4_bool_s9_has__repr_s11___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = _l_s4_bool_s9_has__repr_s11___closed__2;
lean::inc(x_3);
return x_3;
}
}
}
obj* _init__l_s4_bool_s9_has__repr_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ff");
return x_0;
}
}
obj* _init__l_s4_bool_s9_has__repr_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("tt");
return x_0;
}
}
obj* _l_s4_bool_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_bool_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s9_decidable_s9_has__repr_s6___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_bool_s9_has__repr_s11___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_5; 
lean::dec(x_0);
x_5 = _l_s4_bool_s9_has__repr_s11___closed__2;
lean::inc(x_5);
return x_5;
}
}
}
obj* _l_s9_decidable_s9_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_decidable_s9_has__repr_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_7);
x_14 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg(x_0, x_1, x_9);
x_19 = lean::string_append(x_16, x_18);
lean::dec(x_18);
return x_19;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_23; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; obj* x_31; unsigned char x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
lean::dec(x_2);
lean::inc(x_0);
x_31 = lean::apply_1(x_0, x_25);
x_32 = 0;
x_33 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg(x_0, x_32, x_27);
x_34 = lean::string_append(x_31, x_33);
lean::dec(x_33);
return x_34;
}
}
}
}
obj* _init__l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", ");
return x_0;
}
}
obj* _l_s4_list_s9_repr__aux_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s9_repr__aux_s6___main_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_list_s9_repr__aux_s6___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_list_s9_repr__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s9_repr__aux_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s9_repr__aux_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = _l_s4_list_s9_repr__aux_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_list_s4_repr_s6___main_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_4);
return x_4;
}
else
{
unsigned char x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
x_6 = 1;
x_7 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg(x_0, x_6, x_1);
x_8 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
}
}
obj* _init__l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[]");
return x_0;
}
}
obj* _init__l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[");
return x_0;
}
}
obj* _init__l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("]");
return x_0;
}
}
obj* _l_s4_list_s4_repr_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_repr_s6___main_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_list_s4_repr_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s4_list_s4_repr_s6___main_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_list_s4_repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_repr_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_list_s9_has__repr_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_repr_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_list_s9_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s9_has__repr_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_unit_s9_has__repr(unsigned char x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s4_unit_s9_has__repr_s11___closed__1;
lean::inc(x_1);
return x_1;
}
}
obj* _init__l_s4_unit_s9_has__repr_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("()");
return x_0;
}
}
obj* _l_s4_unit_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_unit_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s6_option_s9_has__repr_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_4);
return x_4;
}
else
{
obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::apply_1(x_0, x_6);
x_10 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__2;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_15 = lean::string_append(x_12, x_14);
return x_15;
}
}
}
obj* _init__l_s6_option_s9_has__repr_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("none");
return x_0;
}
}
obj* _init__l_s6_option_s9_has__repr_s6___rarg_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(some ");
return x_0;
}
}
obj* _init__l_s6_option_s9_has__repr_s6___rarg_s11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(")");
return x_0;
}
}
obj* _l_s6_option_s9_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_option_s9_has__repr_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s3_sum_s9_has__repr_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_18 = lean::apply_1(x_1, x_15);
x_19 = _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__2;
lean::inc(x_19);
x_21 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_23 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_24 = lean::string_append(x_21, x_23);
return x_24;
}
}
}
obj* _init__l_s3_sum_s9_has__repr_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(inl ");
return x_0;
}
}
obj* _init__l_s3_sum_s9_has__repr_s6___rarg_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(inr ");
return x_0;
}
}
obj* _l_s3_sum_s9_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_sum_s9_has__repr_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_prod_s9_has__repr_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_1(x_0, x_3);
x_9 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_9);
x_11 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_13 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::apply_1(x_1, x_5);
x_16 = lean::string_append(x_14, x_15);
lean::dec(x_15);
x_18 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
x_19 = lean::string_append(x_16, x_18);
return x_19;
}
}
obj* _init__l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(");
return x_0;
}
}
obj* _l_s4_prod_s9_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_prod_s9_has__repr_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s5_sigma_s9_has__repr_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
x_15 = lean::string_append(x_12, x_14);
x_16 = lean::apply_2(x_1, x_3, x_5);
x_17 = lean::string_append(x_15, x_16);
lean::dec(x_16);
x_19 = _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__2;
x_20 = lean::string_append(x_17, x_19);
return x_20;
}
}
obj* _init__l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\xe2\x9f\xa8");
return x_0;
}
}
obj* _init__l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\xe2\x9f\xa9");
return x_0;
}
}
obj* _l_s5_sigma_s9_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_sigma_s9_has__repr_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s7_subtype_s9_has__repr_s6___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s7_subtype_s9_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_subtype_s9_has__repr_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s3_nat_s11_digit__char(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_dec_eq(x_0, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(2u);
x_10 = lean::nat_dec_eq(x_0, x_9);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_10);
x_13 = lean::mk_nat_obj(3u);
x_14 = lean::nat_dec_eq(x_0, x_13);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_14);
x_17 = lean::mk_nat_obj(4u);
x_18 = lean::nat_dec_eq(x_0, x_17);
lean::dec(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_18);
x_21 = lean::mk_nat_obj(5u);
x_22 = lean::nat_dec_eq(x_0, x_21);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_22);
x_25 = lean::mk_nat_obj(6u);
x_26 = lean::nat_dec_eq(x_0, x_25);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_26);
x_29 = lean::mk_nat_obj(7u);
x_30 = lean::nat_dec_eq(x_0, x_29);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_30);
x_33 = lean::mk_nat_obj(8u);
x_34 = lean::nat_dec_eq(x_0, x_33);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_37; obj* x_38; 
lean::dec(x_34);
x_37 = lean::mk_nat_obj(9u);
x_38 = lean::nat_dec_eq(x_0, x_37);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_38);
x_41 = lean::mk_nat_obj(10u);
x_42 = lean::nat_dec_eq(x_0, x_41);
lean::dec(x_41);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_42);
x_45 = lean::mk_nat_obj(11u);
x_46 = lean::nat_dec_eq(x_0, x_45);
lean::dec(x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_49; obj* x_50; 
lean::dec(x_46);
x_49 = lean::mk_nat_obj(12u);
x_50 = lean::nat_dec_eq(x_0, x_49);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_50);
x_53 = lean::mk_nat_obj(13u);
x_54 = lean::nat_dec_eq(x_0, x_53);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_54);
x_57 = lean::mk_nat_obj(14u);
x_58 = lean::nat_dec_eq(x_0, x_57);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_58);
x_61 = lean::mk_nat_obj(15u);
x_62 = lean::nat_dec_eq(x_0, x_61);
lean::dec(x_61);
lean::dec(x_0);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; 
lean::dec(x_62);
x_66 = _l_s3_nat_s11_digit__char_s11___closed__3;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_69; 
lean::dec(x_62);
x_69 = _l_s3_nat_s11_digit__char_s11___closed__6;
lean::inc(x_69);
return x_69;
}
}
else
{
obj* x_73; 
lean::dec(x_0);
lean::dec(x_58);
x_73 = _l_s3_nat_s11_digit__char_s11___closed__9;
lean::inc(x_73);
return x_73;
}
}
else
{
obj* x_77; 
lean::dec(x_0);
lean::dec(x_54);
x_77 = _l_s3_nat_s11_digit__char_s12___closed__12;
lean::inc(x_77);
return x_77;
}
}
else
{
obj* x_81; 
lean::dec(x_50);
lean::dec(x_0);
x_81 = _l_s3_nat_s11_digit__char_s12___closed__15;
lean::inc(x_81);
return x_81;
}
}
else
{
obj* x_85; 
lean::dec(x_46);
lean::dec(x_0);
x_85 = _l_s3_nat_s11_digit__char_s12___closed__18;
lean::inc(x_85);
return x_85;
}
}
else
{
obj* x_89; 
lean::dec(x_0);
lean::dec(x_42);
x_89 = _l_s3_nat_s11_digit__char_s12___closed__21;
lean::inc(x_89);
return x_89;
}
}
else
{
obj* x_93; 
lean::dec(x_0);
lean::dec(x_38);
x_93 = _l_s3_nat_s11_digit__char_s12___closed__24;
lean::inc(x_93);
return x_93;
}
}
else
{
obj* x_97; 
lean::dec(x_0);
lean::dec(x_34);
x_97 = _l_s3_nat_s11_digit__char_s12___closed__27;
lean::inc(x_97);
return x_97;
}
}
else
{
obj* x_101; 
lean::dec(x_0);
lean::dec(x_30);
x_101 = _l_s3_nat_s11_digit__char_s12___closed__30;
lean::inc(x_101);
return x_101;
}
}
else
{
obj* x_105; 
lean::dec(x_0);
lean::dec(x_26);
x_105 = _l_s3_nat_s11_digit__char_s12___closed__33;
lean::inc(x_105);
return x_105;
}
}
else
{
obj* x_109; 
lean::dec(x_0);
lean::dec(x_22);
x_109 = _l_s3_nat_s11_digit__char_s12___closed__36;
lean::inc(x_109);
return x_109;
}
}
else
{
obj* x_113; 
lean::dec(x_18);
lean::dec(x_0);
x_113 = _l_s3_nat_s11_digit__char_s12___closed__39;
lean::inc(x_113);
return x_113;
}
}
else
{
obj* x_117; 
lean::dec(x_14);
lean::dec(x_0);
x_117 = _l_s3_nat_s11_digit__char_s12___closed__42;
lean::inc(x_117);
return x_117;
}
}
else
{
obj* x_121; 
lean::dec(x_10);
lean::dec(x_0);
x_121 = _l_s3_nat_s11_digit__char_s12___closed__45;
lean::inc(x_121);
return x_121;
}
}
else
{
obj* x_125; 
lean::dec(x_6);
lean::dec(x_0);
x_125 = _l_s3_nat_s11_digit__char_s12___closed__48;
lean::inc(x_125);
return x_125;
}
}
else
{
obj* x_129; 
lean::dec(x_0);
lean::dec(x_2);
x_129 = _l_s3_nat_s11_digit__char_s12___closed__51;
lean::inc(x_129);
return x_129;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(42u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(42u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(42u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s11___closed__1;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(42u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s11___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(42u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(102u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(102u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(102u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s11___closed__4;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(102u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s11___closed__5;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(102u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(101u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(101u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(101u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s11___closed__7;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s11___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(101u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s11___closed__8;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(101u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__10() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(100u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(100u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__11() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(100u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__10;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(100u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__11;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(100u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(99u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(99u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(99u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__13;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__15() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(99u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__14;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(99u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__16() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(98u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(98u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__17() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(98u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__16;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__18() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(98u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__17;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(98u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__19() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(97u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(97u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__20() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(97u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__19;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__21() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(97u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__20;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(97u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__22() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(57u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__23() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(57u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__22;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__24() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__23;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(57u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__25() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(56u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(56u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__26() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(56u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__25;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(56u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__26;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(56u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__28() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(55u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(55u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__29() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(55u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__28;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__30() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(55u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__29;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(55u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__31() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(54u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(54u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__32() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(54u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__31;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__33() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(54u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__32;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(54u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__34() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(53u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(53u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__35() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(53u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__34;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__36() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(53u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__35;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(53u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__37() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(52u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(52u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__38() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(52u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__37;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__39() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(52u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__38;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(52u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__40() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(51u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(51u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__41() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(51u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__40;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__42() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(51u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__41;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(51u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__43() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(50u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(50u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__44() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(50u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__43;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__45() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(50u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__44;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(50u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__46() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(49u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(49u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__47() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(49u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__46;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__48() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(49u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__47;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(49u);
return x_9;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__49() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(48u);
x_1 = lean::mk_nat_obj(1114112u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = lean::mk_nat_obj(48u);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__50() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(57343u);
x_1 = lean::mk_nat_obj(48u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
return x_6;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s3_nat_s11_digit__char_s12___closed__49;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init__l_s3_nat_s11_digit__char_s12___closed__51() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(48u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = _l_s3_nat_s11_digit__char_s12___closed__50;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_9; 
lean::dec(x_2);
x_9 = lean::mk_nat_obj(48u);
return x_9;
}
}
}
obj* _l_s3_nat_s11_digit__succ_s6___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_5, x_10);
lean::dec(x_10);
lean::dec(x_5);
x_14 = lean::nat_dec_eq(x_11, x_0);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
lean::dec(x_14);
lean::dec(x_0);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_11);
lean::dec(x_14);
x_20 = _l_s3_nat_s11_digit__succ_s6___main(x_0, x_7);
x_21 = lean::mk_nat_obj(0u);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
return x_22;
}
}
}
}
obj* _l_s3_nat_s11_digit__succ(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s3_nat_s11_digit__succ_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s3_nat_s10_to__digits_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_11 = _l_s3_nat_s10_to__digits_s6___main(x_0, x_7);
x_12 = _l_s3_nat_s11_digit__succ_s6___main(x_0, x_11);
return x_12;
}
else
{
obj* x_16; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_16 = _l_s3_nat_s10_to__digits_s6___main_s11___closed__1;
lean::inc(x_16);
return x_16;
}
}
}
obj* _init__l_s3_nat_s10_to__digits_s6___main_s11___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _l_s3_nat_s10_to__digits(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = _l_s3_nat_s10_to__digits_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s3_nat_s4_repr(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_nat_obj(10u);
x_2 = _l_s3_nat_s10_to__digits_s6___main(x_1, x_0);
x_3 = _l_s4_list_s3_map_s6___main_s4___at_s3_nat_s4_repr_s9___spec__1(x_2);
x_4 = _l_s4_list_s7_reverse_s6___rarg(x_3);
x_5 = lean::string_mk(x_4);
return x_5;
}
}
obj* _l_s4_list_s3_map_s6___main_s4___at_s3_nat_s4_repr_s9___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = _l_s3_nat_s11_digit__char(x_3);
x_9 = _l_s4_list_s3_map_s6___main_s4___at_s3_nat_s4_repr_s9___spec__1(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init__l_s3_nat_s9_has__repr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s4_repr), 1, 0);
return x_0;
}
}
obj* _l_s16_hex__digit__repr(obj* x_0) {
_start:
{
obj* x_1; unsigned x_2; obj* x_4; obj* x_6; 
x_1 = _l_s3_nat_s11_digit__char(x_0);
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_4);
x_6 = lean::string_push(x_4, x_2);
return x_6;
}
}
obj* _l_s13_char__to__hex(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_nat_obj(16u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_div(x_2, x_1);
x_4 = lean::nat_mod(x_2, x_1);
lean::dec(x_1);
lean::dec(x_2);
x_7 = _l_s16_hex__digit__repr(x_3);
x_8 = _l_s16_hex__digit__repr(x_4);
x_9 = lean::string_append(x_7, x_8);
lean::dec(x_8);
return x_9;
}
}
obj* _l_s13_char__to__hex_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s13_char__to__hex(x_1);
return x_2;
}
}
obj* _l_s4_char_s11_quote__core(unsigned x_0) {
_start:
{
unsigned char x_1; unsigned char x_3; unsigned char x_5; unsigned char x_7; obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::mk_nat_obj(10u);
x_10 = lean::mk_nat_obj(55296u);
x_11 = lean::nat_dec_lt(x_9, x_10);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_11);
x_14 = lean::mk_nat_obj(57343u);
x_15 = lean::nat_dec_lt(x_14, x_9);
lean::dec(x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_15);
lean::dec(x_9);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::box_uint32(x_0);
x_21 = lean::nat_dec_eq(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
unsigned char x_25; 
lean::dec(x_21);
x_25 = 0;
x_7 = x_25;
goto lbl_8;
}
else
{
obj* x_27; 
lean::dec(x_21);
x_27 = _l_s4_char_s11_quote__core_s11___closed__5;
lean::inc(x_27);
return x_27;
}
}
else
{
obj* x_30; obj* x_31; 
lean::dec(x_15);
x_30 = lean::mk_nat_obj(1114112u);
x_31 = lean::nat_dec_lt(x_9, x_30);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_9);
lean::dec(x_31);
x_35 = lean::mk_nat_obj(0u);
x_36 = lean::box_uint32(x_0);
x_37 = lean::nat_dec_eq(x_36, x_35);
lean::dec(x_35);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
unsigned char x_41; 
lean::dec(x_37);
x_41 = 0;
x_7 = x_41;
goto lbl_8;
}
else
{
obj* x_43; 
lean::dec(x_37);
x_43 = _l_s4_char_s11_quote__core_s11___closed__5;
lean::inc(x_43);
return x_43;
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_31);
x_46 = lean::box_uint32(x_0);
x_47 = lean::nat_dec_eq(x_46, x_9);
lean::dec(x_9);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
unsigned char x_51; 
lean::dec(x_47);
x_51 = 0;
x_7 = x_51;
goto lbl_8;
}
else
{
obj* x_53; 
lean::dec(x_47);
x_53 = _l_s4_char_s11_quote__core_s11___closed__5;
lean::inc(x_53);
return x_53;
}
}
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_11);
x_56 = lean::box_uint32(x_0);
x_57 = lean::nat_dec_eq(x_56, x_9);
lean::dec(x_9);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
unsigned char x_61; 
lean::dec(x_57);
x_61 = 0;
x_7 = x_61;
goto lbl_8;
}
else
{
obj* x_63; 
lean::dec(x_57);
x_63 = _l_s4_char_s11_quote__core_s11___closed__5;
lean::inc(x_63);
return x_63;
}
}
lbl_2:
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::mk_nat_obj(31u);
x_66 = lean::box_uint32(x_0);
x_67 = lean::nat_dec_le(x_66, x_65);
lean::dec(x_65);
if (lean::obj_tag(x_67) == 0)
{
obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_67);
x_70 = lean::mk_nat_obj(127u);
x_71 = lean::mk_nat_obj(55296u);
x_72 = lean::nat_dec_lt(x_70, x_71);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_76; 
lean::dec(x_72);
x_75 = lean::mk_nat_obj(57343u);
x_76 = lean::nat_dec_lt(x_75, x_70);
lean::dec(x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_80; obj* x_81; 
lean::dec(x_76);
lean::dec(x_70);
x_80 = lean::mk_nat_obj(0u);
x_81 = lean::nat_dec_eq(x_66, x_80);
lean::dec(x_80);
lean::dec(x_66);
if (lean::obj_tag(x_81) == 0)
{
obj* x_85; obj* x_87; 
lean::dec(x_81);
x_85 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_85);
x_87 = lean::string_push(x_85, x_0);
return x_87;
}
else
{
obj* x_89; obj* x_90; obj* x_92; 
lean::dec(x_81);
x_89 = _l_s13_char__to__hex(x_0);
x_90 = _l_s4_char_s11_quote__core_s11___closed__1;
lean::inc(x_90);
x_92 = lean::string_append(x_90, x_89);
lean::dec(x_89);
return x_92;
}
}
else
{
obj* x_95; obj* x_96; 
lean::dec(x_76);
x_95 = lean::mk_nat_obj(1114112u);
x_96 = lean::nat_dec_lt(x_70, x_95);
lean::dec(x_95);
if (lean::obj_tag(x_96) == 0)
{
obj* x_100; obj* x_101; 
lean::dec(x_96);
lean::dec(x_70);
x_100 = lean::mk_nat_obj(0u);
x_101 = lean::nat_dec_eq(x_66, x_100);
lean::dec(x_100);
lean::dec(x_66);
if (lean::obj_tag(x_101) == 0)
{
obj* x_105; obj* x_107; 
lean::dec(x_101);
x_105 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_105);
x_107 = lean::string_push(x_105, x_0);
return x_107;
}
else
{
obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_101);
x_109 = _l_s13_char__to__hex(x_0);
x_110 = _l_s4_char_s11_quote__core_s11___closed__1;
lean::inc(x_110);
x_112 = lean::string_append(x_110, x_109);
lean::dec(x_109);
return x_112;
}
}
else
{
obj* x_115; 
lean::dec(x_96);
x_115 = lean::nat_dec_eq(x_66, x_70);
lean::dec(x_70);
lean::dec(x_66);
if (lean::obj_tag(x_115) == 0)
{
obj* x_119; obj* x_121; 
lean::dec(x_115);
x_119 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_119);
x_121 = lean::string_push(x_119, x_0);
return x_121;
}
else
{
obj* x_123; obj* x_124; obj* x_126; 
lean::dec(x_115);
x_123 = _l_s13_char__to__hex(x_0);
x_124 = _l_s4_char_s11_quote__core_s11___closed__1;
lean::inc(x_124);
x_126 = lean::string_append(x_124, x_123);
lean::dec(x_123);
return x_126;
}
}
}
}
else
{
obj* x_129; 
lean::dec(x_72);
x_129 = lean::nat_dec_eq(x_66, x_70);
lean::dec(x_70);
lean::dec(x_66);
if (lean::obj_tag(x_129) == 0)
{
obj* x_133; obj* x_135; 
lean::dec(x_129);
x_133 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_133);
x_135 = lean::string_push(x_133, x_0);
return x_135;
}
else
{
obj* x_137; obj* x_138; obj* x_140; 
lean::dec(x_129);
x_137 = _l_s13_char__to__hex(x_0);
x_138 = _l_s4_char_s11_quote__core_s11___closed__1;
lean::inc(x_138);
x_140 = lean::string_append(x_138, x_137);
lean::dec(x_137);
return x_140;
}
}
}
else
{
obj* x_144; obj* x_145; obj* x_147; 
lean::dec(x_66);
lean::dec(x_67);
x_144 = _l_s13_char__to__hex(x_0);
x_145 = _l_s4_char_s11_quote__core_s11___closed__1;
lean::inc(x_145);
x_147 = lean::string_append(x_145, x_144);
lean::dec(x_144);
return x_147;
}
}
lbl_4:
{
obj* x_149; obj* x_150; obj* x_151; 
x_149 = lean::mk_nat_obj(34u);
x_150 = lean::mk_nat_obj(55296u);
x_151 = lean::nat_dec_lt(x_149, x_150);
lean::dec(x_150);
if (lean::obj_tag(x_151) == 0)
{
obj* x_154; obj* x_155; 
lean::dec(x_151);
x_154 = lean::mk_nat_obj(57343u);
x_155 = lean::nat_dec_lt(x_154, x_149);
lean::dec(x_154);
if (lean::obj_tag(x_155) == 0)
{
obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_155);
lean::dec(x_149);
x_159 = lean::mk_nat_obj(0u);
x_160 = lean::box_uint32(x_0);
x_161 = lean::nat_dec_eq(x_160, x_159);
lean::dec(x_159);
lean::dec(x_160);
if (lean::obj_tag(x_161) == 0)
{
unsigned char x_165; 
lean::dec(x_161);
x_165 = 0;
x_1 = x_165;
goto lbl_2;
}
else
{
obj* x_167; 
lean::dec(x_161);
x_167 = _l_s4_char_s11_quote__core_s11___closed__2;
lean::inc(x_167);
return x_167;
}
}
else
{
obj* x_170; obj* x_171; 
lean::dec(x_155);
x_170 = lean::mk_nat_obj(1114112u);
x_171 = lean::nat_dec_lt(x_149, x_170);
lean::dec(x_170);
if (lean::obj_tag(x_171) == 0)
{
obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_149);
lean::dec(x_171);
x_175 = lean::mk_nat_obj(0u);
x_176 = lean::box_uint32(x_0);
x_177 = lean::nat_dec_eq(x_176, x_175);
lean::dec(x_175);
lean::dec(x_176);
if (lean::obj_tag(x_177) == 0)
{
unsigned char x_181; 
lean::dec(x_177);
x_181 = 0;
x_1 = x_181;
goto lbl_2;
}
else
{
obj* x_183; 
lean::dec(x_177);
x_183 = _l_s4_char_s11_quote__core_s11___closed__2;
lean::inc(x_183);
return x_183;
}
}
else
{
obj* x_186; obj* x_187; 
lean::dec(x_171);
x_186 = lean::box_uint32(x_0);
x_187 = lean::nat_dec_eq(x_186, x_149);
lean::dec(x_149);
lean::dec(x_186);
if (lean::obj_tag(x_187) == 0)
{
unsigned char x_191; 
lean::dec(x_187);
x_191 = 0;
x_1 = x_191;
goto lbl_2;
}
else
{
obj* x_193; 
lean::dec(x_187);
x_193 = _l_s4_char_s11_quote__core_s11___closed__2;
lean::inc(x_193);
return x_193;
}
}
}
}
else
{
obj* x_196; obj* x_197; 
lean::dec(x_151);
x_196 = lean::box_uint32(x_0);
x_197 = lean::nat_dec_eq(x_196, x_149);
lean::dec(x_149);
lean::dec(x_196);
if (lean::obj_tag(x_197) == 0)
{
unsigned char x_201; 
lean::dec(x_197);
x_201 = 0;
x_1 = x_201;
goto lbl_2;
}
else
{
obj* x_203; 
lean::dec(x_197);
x_203 = _l_s4_char_s11_quote__core_s11___closed__2;
lean::inc(x_203);
return x_203;
}
}
}
lbl_6:
{
obj* x_205; obj* x_206; obj* x_207; 
x_205 = lean::mk_nat_obj(92u);
x_206 = lean::mk_nat_obj(55296u);
x_207 = lean::nat_dec_lt(x_205, x_206);
lean::dec(x_206);
if (lean::obj_tag(x_207) == 0)
{
obj* x_210; obj* x_211; 
lean::dec(x_207);
x_210 = lean::mk_nat_obj(57343u);
x_211 = lean::nat_dec_lt(x_210, x_205);
lean::dec(x_210);
if (lean::obj_tag(x_211) == 0)
{
obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_211);
lean::dec(x_205);
x_215 = lean::mk_nat_obj(0u);
x_216 = lean::box_uint32(x_0);
x_217 = lean::nat_dec_eq(x_216, x_215);
lean::dec(x_215);
lean::dec(x_216);
if (lean::obj_tag(x_217) == 0)
{
unsigned char x_221; 
lean::dec(x_217);
x_221 = 0;
x_3 = x_221;
goto lbl_4;
}
else
{
obj* x_223; 
lean::dec(x_217);
x_223 = _l_s4_char_s11_quote__core_s11___closed__3;
lean::inc(x_223);
return x_223;
}
}
else
{
obj* x_226; obj* x_227; 
lean::dec(x_211);
x_226 = lean::mk_nat_obj(1114112u);
x_227 = lean::nat_dec_lt(x_205, x_226);
lean::dec(x_226);
if (lean::obj_tag(x_227) == 0)
{
obj* x_231; obj* x_232; obj* x_233; 
lean::dec(x_227);
lean::dec(x_205);
x_231 = lean::mk_nat_obj(0u);
x_232 = lean::box_uint32(x_0);
x_233 = lean::nat_dec_eq(x_232, x_231);
lean::dec(x_231);
lean::dec(x_232);
if (lean::obj_tag(x_233) == 0)
{
unsigned char x_237; 
lean::dec(x_233);
x_237 = 0;
x_3 = x_237;
goto lbl_4;
}
else
{
obj* x_239; 
lean::dec(x_233);
x_239 = _l_s4_char_s11_quote__core_s11___closed__3;
lean::inc(x_239);
return x_239;
}
}
else
{
obj* x_242; obj* x_243; 
lean::dec(x_227);
x_242 = lean::box_uint32(x_0);
x_243 = lean::nat_dec_eq(x_242, x_205);
lean::dec(x_205);
lean::dec(x_242);
if (lean::obj_tag(x_243) == 0)
{
unsigned char x_247; 
lean::dec(x_243);
x_247 = 0;
x_3 = x_247;
goto lbl_4;
}
else
{
obj* x_249; 
lean::dec(x_243);
x_249 = _l_s4_char_s11_quote__core_s11___closed__3;
lean::inc(x_249);
return x_249;
}
}
}
}
else
{
obj* x_252; obj* x_253; 
lean::dec(x_207);
x_252 = lean::box_uint32(x_0);
x_253 = lean::nat_dec_eq(x_252, x_205);
lean::dec(x_205);
lean::dec(x_252);
if (lean::obj_tag(x_253) == 0)
{
unsigned char x_257; 
lean::dec(x_253);
x_257 = 0;
x_3 = x_257;
goto lbl_4;
}
else
{
obj* x_259; 
lean::dec(x_253);
x_259 = _l_s4_char_s11_quote__core_s11___closed__3;
lean::inc(x_259);
return x_259;
}
}
}
lbl_8:
{
obj* x_261; obj* x_262; obj* x_263; 
x_261 = lean::mk_nat_obj(9u);
x_262 = lean::mk_nat_obj(55296u);
x_263 = lean::nat_dec_lt(x_261, x_262);
lean::dec(x_262);
if (lean::obj_tag(x_263) == 0)
{
obj* x_266; obj* x_267; 
lean::dec(x_263);
x_266 = lean::mk_nat_obj(57343u);
x_267 = lean::nat_dec_lt(x_266, x_261);
lean::dec(x_266);
if (lean::obj_tag(x_267) == 0)
{
obj* x_271; obj* x_272; obj* x_273; 
lean::dec(x_261);
lean::dec(x_267);
x_271 = lean::mk_nat_obj(0u);
x_272 = lean::box_uint32(x_0);
x_273 = lean::nat_dec_eq(x_272, x_271);
lean::dec(x_271);
lean::dec(x_272);
if (lean::obj_tag(x_273) == 0)
{
unsigned char x_277; 
lean::dec(x_273);
x_277 = 0;
x_5 = x_277;
goto lbl_6;
}
else
{
obj* x_279; 
lean::dec(x_273);
x_279 = _l_s4_char_s11_quote__core_s11___closed__4;
lean::inc(x_279);
return x_279;
}
}
else
{
obj* x_282; obj* x_283; 
lean::dec(x_267);
x_282 = lean::mk_nat_obj(1114112u);
x_283 = lean::nat_dec_lt(x_261, x_282);
lean::dec(x_282);
if (lean::obj_tag(x_283) == 0)
{
obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_261);
lean::dec(x_283);
x_287 = lean::mk_nat_obj(0u);
x_288 = lean::box_uint32(x_0);
x_289 = lean::nat_dec_eq(x_288, x_287);
lean::dec(x_287);
lean::dec(x_288);
if (lean::obj_tag(x_289) == 0)
{
unsigned char x_293; 
lean::dec(x_289);
x_293 = 0;
x_5 = x_293;
goto lbl_6;
}
else
{
obj* x_295; 
lean::dec(x_289);
x_295 = _l_s4_char_s11_quote__core_s11___closed__4;
lean::inc(x_295);
return x_295;
}
}
else
{
obj* x_298; obj* x_299; 
lean::dec(x_283);
x_298 = lean::box_uint32(x_0);
x_299 = lean::nat_dec_eq(x_298, x_261);
lean::dec(x_261);
lean::dec(x_298);
if (lean::obj_tag(x_299) == 0)
{
unsigned char x_303; 
lean::dec(x_299);
x_303 = 0;
x_5 = x_303;
goto lbl_6;
}
else
{
obj* x_305; 
lean::dec(x_299);
x_305 = _l_s4_char_s11_quote__core_s11___closed__4;
lean::inc(x_305);
return x_305;
}
}
}
}
else
{
obj* x_308; obj* x_309; 
lean::dec(x_263);
x_308 = lean::box_uint32(x_0);
x_309 = lean::nat_dec_eq(x_308, x_261);
lean::dec(x_261);
lean::dec(x_308);
if (lean::obj_tag(x_309) == 0)
{
unsigned char x_313; 
lean::dec(x_309);
x_313 = 0;
x_5 = x_313;
goto lbl_6;
}
else
{
obj* x_315; 
lean::dec(x_309);
x_315 = _l_s4_char_s11_quote__core_s11___closed__4;
lean::inc(x_315);
return x_315;
}
}
}
}
}
obj* _init__l_s4_char_s11_quote__core_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\x");
return x_0;
}
}
obj* _init__l_s4_char_s11_quote__core_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\\"");
return x_0;
}
}
obj* _init__l_s4_char_s11_quote__core_s11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\\\");
return x_0;
}
}
obj* _init__l_s4_char_s11_quote__core_s11___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\t");
return x_0;
}
}
obj* _init__l_s4_char_s11_quote__core_s11___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\n");
return x_0;
}
}
obj* _l_s4_char_s11_quote__core_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s11_quote__core(x_1);
return x_2;
}
}
obj* _l_s4_char_s9_has__repr(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; 
x_1 = _l_s4_char_s11_quote__core(x_0);
x_2 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_6 = lean::string_append(x_4, x_2);
return x_6;
}
}
obj* _init__l_s4_char_s9_has__repr_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("'");
return x_0;
}
}
obj* _l_s4_char_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s6_string_s10_quote__aux_s6___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; unsigned x_9; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_11 = _l_s4_char_s11_quote__core(x_9);
x_12 = _l_s6_string_s10_quote__aux_s6___main(x_6);
x_13 = lean::string_append(x_11, x_12);
lean::dec(x_12);
return x_13;
}
}
}
obj* _l_s6_string_s10_quote__aux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s6_string_s10_quote__aux_s6___main(x_0);
return x_1;
}
}
obj* _l_s6_string_s5_quote(obj* x_0) {
_start:
{
unsigned char x_2; 
lean::inc(x_0);
x_2 = _l_s6_string_s9_is__empty(x_0);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_3 = lean::string_data(x_0);
x_4 = _l_s6_string_s10_quote__aux_s6___main(x_3);
x_5 = _l_s6_string_s5_quote_s11___closed__1;
lean::inc(x_5);
x_7 = lean::string_append(x_5, x_4);
lean::dec(x_4);
x_9 = lean::string_append(x_7, x_5);
return x_9;
}
else
{
obj* x_11; 
lean::dec(x_0);
x_11 = _l_s6_string_s5_quote_s11___closed__2;
lean::inc(x_11);
return x_11;
}
}
}
obj* _init__l_s6_string_s5_quote_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\"");
return x_0;
}
}
obj* _init__l_s6_string_s5_quote_s11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\"\"");
return x_0;
}
}
obj* _init__l_s6_string_s9_has__repr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_string_s5_quote), 1, 0);
return x_0;
}
}
obj* _l_s6_string_s8_iterator_s9_has__repr(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
x_3 = _l_s6_string_s5_quote(x_1);
x_4 = _l_s6_string_s8_iterator_s9_has__repr_s11___closed__1;
x_5 = lean::string_append(x_3, x_4);
return x_5;
}
}
obj* _init__l_s6_string_s8_iterator_s9_has__repr_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(".mk_iterator");
return x_0;
}
}
obj* _l_s3_fin_s9_has__repr_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s3_nat_s4_repr(x_0);
return x_1;
}
}
obj* _l_s3_fin_s9_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s9_has__repr_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s6_uint16_s9_has__repr(unsigned short x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint16_to_nat(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s6_uint16_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned short x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s6_uint16_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s6_uint32_s9_has__repr(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s6_uint32_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s6_uint32_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s6_uint64_s9_has__repr(unsigned long long x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint64_to_nat(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s6_uint64_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
unsigned long long x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = _l_s6_uint64_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s5_usize_s9_has__repr(size_t x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::usize_to_nat(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s5_usize_s9_has__repr_s7___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = _l_s5_usize_s9_has__repr(x_1);
return x_2;
}
}
obj* _l_s4_char_s4_repr(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; 
x_1 = _l_s4_char_s11_quote__core(x_0);
x_2 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_6 = lean::string_append(x_4, x_2);
return x_6;
}
}
obj* _l_s4_char_s4_repr_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s4_repr(x_1);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
void _l_initialize__l_s4_init_s4_data_s4_uint();
void _l_initialize__l_s4_init_s4_data_s5_usize();
void _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s4_repr() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_initialize__l_s4_init_s4_data_s4_uint();
 _l_initialize__l_s4_init_s4_data_s5_usize();
 _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
 _l_s4_bool_s9_has__repr_s11___closed__1 = _init__l_s4_bool_s9_has__repr_s11___closed__1();
 _l_s4_bool_s9_has__repr_s11___closed__2 = _init__l_s4_bool_s9_has__repr_s11___closed__2();
 _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1 = _init__l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1();
 _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__1 = _init__l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__1();
 _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2 = _init__l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2();
 _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3 = _init__l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3();
 _l_s4_unit_s9_has__repr_s11___closed__1 = _init__l_s4_unit_s9_has__repr_s11___closed__1();
 _l_s6_option_s9_has__repr_s6___rarg_s11___closed__1 = _init__l_s6_option_s9_has__repr_s6___rarg_s11___closed__1();
 _l_s6_option_s9_has__repr_s6___rarg_s11___closed__2 = _init__l_s6_option_s9_has__repr_s6___rarg_s11___closed__2();
 _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3 = _init__l_s6_option_s9_has__repr_s6___rarg_s11___closed__3();
 _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__1 = _init__l_s3_sum_s9_has__repr_s6___rarg_s11___closed__1();
 _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__2 = _init__l_s3_sum_s9_has__repr_s6___rarg_s11___closed__2();
 _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1 = _init__l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1();
 _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__1 = _init__l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__1();
 _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__2 = _init__l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__2();
 _l_s3_nat_s11_digit__char_s11___closed__1 = _init__l_s3_nat_s11_digit__char_s11___closed__1();
 _l_s3_nat_s11_digit__char_s11___closed__2 = _init__l_s3_nat_s11_digit__char_s11___closed__2();
 _l_s3_nat_s11_digit__char_s11___closed__3 = _init__l_s3_nat_s11_digit__char_s11___closed__3();
 _l_s3_nat_s11_digit__char_s11___closed__4 = _init__l_s3_nat_s11_digit__char_s11___closed__4();
 _l_s3_nat_s11_digit__char_s11___closed__5 = _init__l_s3_nat_s11_digit__char_s11___closed__5();
 _l_s3_nat_s11_digit__char_s11___closed__6 = _init__l_s3_nat_s11_digit__char_s11___closed__6();
 _l_s3_nat_s11_digit__char_s11___closed__7 = _init__l_s3_nat_s11_digit__char_s11___closed__7();
 _l_s3_nat_s11_digit__char_s11___closed__8 = _init__l_s3_nat_s11_digit__char_s11___closed__8();
 _l_s3_nat_s11_digit__char_s11___closed__9 = _init__l_s3_nat_s11_digit__char_s11___closed__9();
 _l_s3_nat_s11_digit__char_s12___closed__10 = _init__l_s3_nat_s11_digit__char_s12___closed__10();
 _l_s3_nat_s11_digit__char_s12___closed__11 = _init__l_s3_nat_s11_digit__char_s12___closed__11();
 _l_s3_nat_s11_digit__char_s12___closed__12 = _init__l_s3_nat_s11_digit__char_s12___closed__12();
 _l_s3_nat_s11_digit__char_s12___closed__13 = _init__l_s3_nat_s11_digit__char_s12___closed__13();
 _l_s3_nat_s11_digit__char_s12___closed__14 = _init__l_s3_nat_s11_digit__char_s12___closed__14();
 _l_s3_nat_s11_digit__char_s12___closed__15 = _init__l_s3_nat_s11_digit__char_s12___closed__15();
 _l_s3_nat_s11_digit__char_s12___closed__16 = _init__l_s3_nat_s11_digit__char_s12___closed__16();
 _l_s3_nat_s11_digit__char_s12___closed__17 = _init__l_s3_nat_s11_digit__char_s12___closed__17();
 _l_s3_nat_s11_digit__char_s12___closed__18 = _init__l_s3_nat_s11_digit__char_s12___closed__18();
 _l_s3_nat_s11_digit__char_s12___closed__19 = _init__l_s3_nat_s11_digit__char_s12___closed__19();
 _l_s3_nat_s11_digit__char_s12___closed__20 = _init__l_s3_nat_s11_digit__char_s12___closed__20();
 _l_s3_nat_s11_digit__char_s12___closed__21 = _init__l_s3_nat_s11_digit__char_s12___closed__21();
 _l_s3_nat_s11_digit__char_s12___closed__22 = _init__l_s3_nat_s11_digit__char_s12___closed__22();
 _l_s3_nat_s11_digit__char_s12___closed__23 = _init__l_s3_nat_s11_digit__char_s12___closed__23();
 _l_s3_nat_s11_digit__char_s12___closed__24 = _init__l_s3_nat_s11_digit__char_s12___closed__24();
 _l_s3_nat_s11_digit__char_s12___closed__25 = _init__l_s3_nat_s11_digit__char_s12___closed__25();
 _l_s3_nat_s11_digit__char_s12___closed__26 = _init__l_s3_nat_s11_digit__char_s12___closed__26();
 _l_s3_nat_s11_digit__char_s12___closed__27 = _init__l_s3_nat_s11_digit__char_s12___closed__27();
 _l_s3_nat_s11_digit__char_s12___closed__28 = _init__l_s3_nat_s11_digit__char_s12___closed__28();
 _l_s3_nat_s11_digit__char_s12___closed__29 = _init__l_s3_nat_s11_digit__char_s12___closed__29();
 _l_s3_nat_s11_digit__char_s12___closed__30 = _init__l_s3_nat_s11_digit__char_s12___closed__30();
 _l_s3_nat_s11_digit__char_s12___closed__31 = _init__l_s3_nat_s11_digit__char_s12___closed__31();
 _l_s3_nat_s11_digit__char_s12___closed__32 = _init__l_s3_nat_s11_digit__char_s12___closed__32();
 _l_s3_nat_s11_digit__char_s12___closed__33 = _init__l_s3_nat_s11_digit__char_s12___closed__33();
 _l_s3_nat_s11_digit__char_s12___closed__34 = _init__l_s3_nat_s11_digit__char_s12___closed__34();
 _l_s3_nat_s11_digit__char_s12___closed__35 = _init__l_s3_nat_s11_digit__char_s12___closed__35();
 _l_s3_nat_s11_digit__char_s12___closed__36 = _init__l_s3_nat_s11_digit__char_s12___closed__36();
 _l_s3_nat_s11_digit__char_s12___closed__37 = _init__l_s3_nat_s11_digit__char_s12___closed__37();
 _l_s3_nat_s11_digit__char_s12___closed__38 = _init__l_s3_nat_s11_digit__char_s12___closed__38();
 _l_s3_nat_s11_digit__char_s12___closed__39 = _init__l_s3_nat_s11_digit__char_s12___closed__39();
 _l_s3_nat_s11_digit__char_s12___closed__40 = _init__l_s3_nat_s11_digit__char_s12___closed__40();
 _l_s3_nat_s11_digit__char_s12___closed__41 = _init__l_s3_nat_s11_digit__char_s12___closed__41();
 _l_s3_nat_s11_digit__char_s12___closed__42 = _init__l_s3_nat_s11_digit__char_s12___closed__42();
 _l_s3_nat_s11_digit__char_s12___closed__43 = _init__l_s3_nat_s11_digit__char_s12___closed__43();
 _l_s3_nat_s11_digit__char_s12___closed__44 = _init__l_s3_nat_s11_digit__char_s12___closed__44();
 _l_s3_nat_s11_digit__char_s12___closed__45 = _init__l_s3_nat_s11_digit__char_s12___closed__45();
 _l_s3_nat_s11_digit__char_s12___closed__46 = _init__l_s3_nat_s11_digit__char_s12___closed__46();
 _l_s3_nat_s11_digit__char_s12___closed__47 = _init__l_s3_nat_s11_digit__char_s12___closed__47();
 _l_s3_nat_s11_digit__char_s12___closed__48 = _init__l_s3_nat_s11_digit__char_s12___closed__48();
 _l_s3_nat_s11_digit__char_s12___closed__49 = _init__l_s3_nat_s11_digit__char_s12___closed__49();
 _l_s3_nat_s11_digit__char_s12___closed__50 = _init__l_s3_nat_s11_digit__char_s12___closed__50();
 _l_s3_nat_s11_digit__char_s12___closed__51 = _init__l_s3_nat_s11_digit__char_s12___closed__51();
 _l_s3_nat_s10_to__digits_s6___main_s11___closed__1 = _init__l_s3_nat_s10_to__digits_s6___main_s11___closed__1();
 _l_s3_nat_s9_has__repr = _init__l_s3_nat_s9_has__repr();
 _l_s4_char_s11_quote__core_s11___closed__1 = _init__l_s4_char_s11_quote__core_s11___closed__1();
 _l_s4_char_s11_quote__core_s11___closed__2 = _init__l_s4_char_s11_quote__core_s11___closed__2();
 _l_s4_char_s11_quote__core_s11___closed__3 = _init__l_s4_char_s11_quote__core_s11___closed__3();
 _l_s4_char_s11_quote__core_s11___closed__4 = _init__l_s4_char_s11_quote__core_s11___closed__4();
 _l_s4_char_s11_quote__core_s11___closed__5 = _init__l_s4_char_s11_quote__core_s11___closed__5();
 _l_s4_char_s9_has__repr_s11___closed__1 = _init__l_s4_char_s9_has__repr_s11___closed__1();
 _l_s6_string_s5_quote_s11___closed__1 = _init__l_s6_string_s5_quote_s11___closed__1();
 _l_s6_string_s5_quote_s11___closed__2 = _init__l_s6_string_s5_quote_s11___closed__2();
 _l_s6_string_s9_has__repr = _init__l_s6_string_s9_has__repr();
 _l_s6_string_s8_iterator_s9_has__repr_s11___closed__1 = _init__l_s6_string_s8_iterator_s9_has__repr_s11___closed__1();
}

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
obj* l_list_map___main___at_nat_repr___spec__1(obj*);
obj* l_usize_has__repr(size_t);
obj* l_nat_digit__char___closed__22;
obj* l_nat_digit__char(obj*);
obj* l_nat_digit__char___closed__37;
obj* l_list_repr___main___rarg(obj*, obj*);
obj* l_nat_digit__char___closed__35;
obj* l_string_quote__aux(obj*);
obj* l_string_iterator_has__repr___closed__1;
obj* l_nat_digit__char___closed__29;
obj* l_nat_digit__char___closed__15;
obj* l_option_has__repr___rarg___closed__2;
obj* l_id_has__repr___rarg(obj*);
obj* l_string_has__repr;
obj* l_nat_digit__char___closed__5;
obj* l_fin_has__repr(obj*);
obj* l_nat_digit__char___closed__14;
obj* l_list_repr__aux___rarg___boxed(obj*, obj*, obj*);
obj* l_nat_digit__char___closed__30;
obj* l_nat_digit__char___closed__16;
obj* l_uint32_has__repr(unsigned);
obj* l_unit_has__repr___closed__1;
obj* l_nat_digit__char___closed__38;
obj* l_list_repr__aux___main(obj*);
obj* l_nat_digit__char___closed__1;
obj* l_char_quote__core___boxed(obj*);
obj* l_nat_digit__char___closed__11;
obj* l_list_reverse___rarg(obj*);
obj* l_nat_digit__char___closed__3;
obj* l_uint16_has__repr(unsigned short);
obj* l_nat_digit__char___closed__45;
obj* l_fin_has__repr___rarg(obj*);
obj* l_nat_has__repr;
obj* l_char_repr(unsigned);
obj* l_nat_digit__char___closed__9;
obj* l_string_quote(obj*);
obj* l_nat_to__digits___main(obj*, obj*);
obj* l_sum_has__repr___rarg___closed__1;
obj* l_option_has__repr___rarg___closed__1;
obj* l_id_has__repr(obj*);
unsigned char l_string_is__empty(obj*);
obj* l_list_repr___main___rarg___closed__1;
obj* l_option_has__repr(obj*);
obj* l_nat_digit__char___closed__34;
obj* l_hex__digit__repr(obj*);
obj* l_char_quote__core___closed__2;
obj* l_usize_has__repr___boxed(obj*);
obj* l_string_quote__aux___main(obj*);
obj* l_char_quote__core___closed__1;
obj* l_nat_digit__char___closed__40;
obj* l_bool_has__repr___boxed(obj*);
obj* l_nat_digit__succ___main(obj*, obj*);
obj* l_nat_to__digits(obj*, obj*);
obj* l_sigma_has__repr(obj*, obj*);
obj* l_sum_has__repr___rarg___closed__2;
obj* l_sum_has__repr(obj*, obj*);
obj* l_nat_digit__char___closed__28;
obj* l_nat_digit__char___closed__18;
obj* l_char_quote__core___closed__4;
obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_char_has__repr___boxed(obj*);
obj* l_char_quote__core___closed__5;
obj* l_string_iterator_has__repr(obj*);
obj* l_nat_digit__char___closed__8;
obj* l_list_repr___main___rarg___closed__3;
obj* l_char_has__repr___closed__1;
obj* l_nat_digit__char___closed__7;
obj* l_decidable_has__repr(obj*);
obj* l_string_quote___closed__1;
obj* l_bool_has__repr(unsigned char);
obj* l_list_repr___rarg(obj*, obj*);
obj* l_nat_digit__char___closed__47;
extern obj* l_string_join___closed__1;
obj* l_list_has__repr(obj*);
obj* l_char__to__hex___boxed(obj*);
obj* l_nat_digit__char___closed__12;
obj* l_sigma_has__repr___rarg___closed__1;
obj* l_nat_digit__char___closed__44;
obj* l_nat_digit__char___closed__32;
obj* l_uint64_has__repr(unsigned long long);
obj* l_string_quote___closed__2;
obj* l_nat_digit__char___closed__51;
obj* l_list_repr__aux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_char_quote__core___closed__3;
obj* l_char_repr___boxed(obj*);
obj* l_char_has__repr(unsigned);
obj* l_nat_digit__char___closed__24;
obj* l_list_has__repr___rarg(obj*);
obj* l_option_has__repr___rarg(obj*, obj*);
obj* l_list_repr___main___rarg___closed__2;
obj* l_nat_digit__char___closed__2;
obj* l_list_repr__aux(obj*);
obj* l_bool_has__repr___closed__2;
obj* l_prod_has__repr___rarg___closed__1;
obj* l_nat_digit__char___closed__23;
obj* l_sigma_has__repr___rarg(obj*, obj*, obj*);
obj* l_uint32_has__repr___boxed(obj*);
obj* l_uint64_has__repr___boxed(obj*);
obj* l_subtype_has__repr___rarg(obj*, obj*);
obj* l_nat_digit__char___closed__49;
obj* l_nat_digit__char___closed__46;
obj* l_decidable_has__repr___rarg(obj*);
obj* l_nat_digit__char___closed__50;
obj* l_nat_digit__char___closed__27;
obj* l_nat_digit__char___closed__36;
obj* l_nat_digit__char___closed__19;
obj* l_nat_to__digits___main___closed__1;
obj* l_nat_digit__char___closed__43;
obj* l_sum_has__repr___rarg(obj*, obj*, obj*);
obj* l_bool_has__repr___closed__1;
obj* l_nat_digit__succ(obj*, obj*);
obj* l_prod_has__repr(obj*, obj*);
obj* l_list_repr(obj*);
obj* l_subtype_has__repr(obj*, obj*);
obj* l_list_repr___main(obj*);
obj* l_nat_repr(obj*);
obj* l_prod_has__repr___rarg(obj*, obj*, obj*);
obj* l_nat_digit__char___closed__41;
obj* l_sigma_has__repr___rarg___closed__2;
obj* l_nat_digit__char___closed__25;
obj* l_nat_digit__char___closed__48;
obj* l_nat_digit__char___closed__4;
obj* l_char__to__hex(unsigned);
obj* l_nat_digit__char___closed__31;
obj* l_option_has__repr___rarg___closed__3;
obj* l_nat_digit__char___closed__13;
obj* l_unit_has__repr(obj*);
obj* l_nat_digit__char___closed__26;
obj* l_nat_digit__char___closed__42;
obj* l_nat_digit__char___closed__17;
obj* l_nat_digit__char___closed__10;
obj* l_char_quote__core(unsigned);
obj* l_nat_digit__char___closed__20;
obj* l_list_repr__aux___main___rarg(obj*, unsigned char, obj*);
obj* l_nat_digit__char___closed__39;
obj* l_nat_digit__char___closed__33;
obj* l_nat_digit__char___closed__6;
obj* l_nat_digit__char___closed__21;
obj* l_uint16_has__repr___boxed(obj*);
obj* l_list_repr__aux___rarg(obj*, unsigned char, obj*);
obj* l_id_has__repr___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_id_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id_has__repr___rarg), 1, 0);
return x_2;
}
}
obj* l_bool_has__repr(unsigned char x_0) {
_start:
{
if (x_0 == 0)
{
obj* x_1; 
x_1 = l_bool_has__repr___closed__1;
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = l_bool_has__repr___closed__2;
lean::inc(x_3);
return x_3;
}
}
}
obj* _init_l_bool_has__repr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ff");
return x_0;
}
}
obj* _init_l_bool_has__repr___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("tt");
return x_0;
}
}
obj* l_bool_has__repr___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_bool_has__repr(x_1);
return x_2;
}
}
obj* l_decidable_has__repr___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_bool_has__repr___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_5; 
lean::dec(x_0);
x_5 = l_bool_has__repr___closed__2;
lean::inc(x_5);
return x_5;
}
}
}
obj* l_decidable_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_has__repr___rarg), 1, 0);
return x_2;
}
}
obj* l_list_repr__aux___main___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = l_string_join___closed__1;
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
x_14 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = l_list_repr__aux___main___rarg(x_0, x_1, x_9);
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
x_23 = l_string_join___closed__1;
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
x_33 = l_list_repr__aux___main___rarg(x_0, x_32, x_27);
x_34 = lean::string_append(x_31, x_33);
lean::dec(x_33);
return x_34;
}
}
}
}
obj* _init_l_list_repr__aux___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", ");
return x_0;
}
}
obj* l_list_repr__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_repr__aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_list_repr__aux___main___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_list_repr__aux___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_repr__aux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_repr__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_repr__aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_list_repr__aux___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_list_repr___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_list_repr___main___rarg___closed__1;
lean::inc(x_4);
return x_4;
}
else
{
unsigned char x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
x_6 = 1;
x_7 = l_list_repr__aux___main___rarg(x_0, x_6, x_1);
x_8 = l_list_repr___main___rarg___closed__2;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = l_list_repr___main___rarg___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
}
}
obj* _init_l_list_repr___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[]");
return x_0;
}
}
obj* _init_l_list_repr___main___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("[");
return x_0;
}
}
obj* _init_l_list_repr___main___rarg___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("]");
return x_0;
}
}
obj* l_list_repr___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_repr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_repr___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___rarg), 2, 0);
return x_2;
}
}
obj* l_list_has__repr___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__repr___rarg), 1, 0);
return x_2;
}
}
obj* l_unit_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_unit_has__repr___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_unit_has__repr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("()");
return x_0;
}
}
obj* l_option_has__repr___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_option_has__repr___rarg___closed__1;
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
x_10 = l_option_has__repr___rarg___closed__2;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = l_option_has__repr___rarg___closed__3;
x_15 = lean::string_append(x_12, x_14);
return x_15;
}
}
}
obj* _init_l_option_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("none");
return x_0;
}
}
obj* _init_l_option_has__repr___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(some ");
return x_0;
}
}
obj* _init_l_option_has__repr___rarg___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(")");
return x_0;
}
}
obj* l_option_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_has__repr___rarg), 2, 0);
return x_2;
}
}
obj* l_sum_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_8 = l_sum_has__repr___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_12 = l_option_has__repr___rarg___closed__3;
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
x_19 = l_sum_has__repr___rarg___closed__2;
lean::inc(x_19);
x_21 = lean::string_append(x_19, x_18);
lean::dec(x_18);
x_23 = l_option_has__repr___rarg___closed__3;
x_24 = lean::string_append(x_21, x_23);
return x_24;
}
}
}
obj* _init_l_sum_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(inl ");
return x_0;
}
}
obj* _init_l_sum_has__repr___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(inr ");
return x_0;
}
}
obj* l_sum_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_has__repr___rarg), 3, 0);
return x_4;
}
}
obj* l_prod_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_1(x_0, x_3);
x_9 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_9);
x_11 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_13 = l_list_repr__aux___main___rarg___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::apply_1(x_1, x_5);
x_16 = lean::string_append(x_14, x_15);
lean::dec(x_15);
x_18 = l_option_has__repr___rarg___closed__3;
x_19 = lean::string_append(x_16, x_18);
return x_19;
}
}
obj* _init_l_prod_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(");
return x_0;
}
}
obj* l_prod_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_has__repr___rarg), 3, 0);
return x_4;
}
}
obj* l_sigma_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_10 = l_sigma_has__repr___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_14 = l_list_repr__aux___main___rarg___closed__1;
x_15 = lean::string_append(x_12, x_14);
x_16 = lean::apply_2(x_1, x_3, x_5);
x_17 = lean::string_append(x_15, x_16);
lean::dec(x_16);
x_19 = l_sigma_has__repr___rarg___closed__2;
x_20 = lean::string_append(x_17, x_19);
return x_20;
}
}
obj* _init_l_sigma_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\xe2\x9f\xa8");
return x_0;
}
}
obj* _init_l_sigma_has__repr___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\xe2\x9f\xa9");
return x_0;
}
}
obj* l_sigma_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_has__repr___rarg), 3, 0);
return x_4;
}
}
obj* l_subtype_has__repr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_subtype_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_has__repr___rarg), 2, 0);
return x_4;
}
}
obj* l_nat_digit__char(obj* x_0) {
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
x_66 = l_nat_digit__char___closed__3;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_69; 
lean::dec(x_62);
x_69 = l_nat_digit__char___closed__6;
lean::inc(x_69);
return x_69;
}
}
else
{
obj* x_73; 
lean::dec(x_0);
lean::dec(x_58);
x_73 = l_nat_digit__char___closed__9;
lean::inc(x_73);
return x_73;
}
}
else
{
obj* x_77; 
lean::dec(x_0);
lean::dec(x_54);
x_77 = l_nat_digit__char___closed__12;
lean::inc(x_77);
return x_77;
}
}
else
{
obj* x_81; 
lean::dec(x_0);
lean::dec(x_50);
x_81 = l_nat_digit__char___closed__15;
lean::inc(x_81);
return x_81;
}
}
else
{
obj* x_85; 
lean::dec(x_0);
lean::dec(x_46);
x_85 = l_nat_digit__char___closed__18;
lean::inc(x_85);
return x_85;
}
}
else
{
obj* x_89; 
lean::dec(x_0);
lean::dec(x_42);
x_89 = l_nat_digit__char___closed__21;
lean::inc(x_89);
return x_89;
}
}
else
{
obj* x_93; 
lean::dec(x_38);
lean::dec(x_0);
x_93 = l_nat_digit__char___closed__24;
lean::inc(x_93);
return x_93;
}
}
else
{
obj* x_97; 
lean::dec(x_0);
lean::dec(x_34);
x_97 = l_nat_digit__char___closed__27;
lean::inc(x_97);
return x_97;
}
}
else
{
obj* x_101; 
lean::dec(x_0);
lean::dec(x_30);
x_101 = l_nat_digit__char___closed__30;
lean::inc(x_101);
return x_101;
}
}
else
{
obj* x_105; 
lean::dec(x_26);
lean::dec(x_0);
x_105 = l_nat_digit__char___closed__33;
lean::inc(x_105);
return x_105;
}
}
else
{
obj* x_109; 
lean::dec(x_0);
lean::dec(x_22);
x_109 = l_nat_digit__char___closed__36;
lean::inc(x_109);
return x_109;
}
}
else
{
obj* x_113; 
lean::dec(x_18);
lean::dec(x_0);
x_113 = l_nat_digit__char___closed__39;
lean::inc(x_113);
return x_113;
}
}
else
{
obj* x_117; 
lean::dec(x_14);
lean::dec(x_0);
x_117 = l_nat_digit__char___closed__42;
lean::inc(x_117);
return x_117;
}
}
else
{
obj* x_121; 
lean::dec(x_10);
lean::dec(x_0);
x_121 = l_nat_digit__char___closed__45;
lean::inc(x_121);
return x_121;
}
}
else
{
obj* x_125; 
lean::dec(x_6);
lean::dec(x_0);
x_125 = l_nat_digit__char___closed__48;
lean::inc(x_125);
return x_125;
}
}
else
{
obj* x_129; 
lean::dec(x_0);
lean::dec(x_2);
x_129 = l_nat_digit__char___closed__51;
lean::inc(x_129);
return x_129;
}
}
}
obj* _init_l_nat_digit__char___closed__1() {
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
obj* _init_l_nat_digit__char___closed__2() {
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
x_8 = l_nat_digit__char___closed__1;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__3() {
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
x_6 = l_nat_digit__char___closed__2;
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
obj* _init_l_nat_digit__char___closed__4() {
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
obj* _init_l_nat_digit__char___closed__5() {
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
x_8 = l_nat_digit__char___closed__4;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__6() {
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
x_6 = l_nat_digit__char___closed__5;
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
obj* _init_l_nat_digit__char___closed__7() {
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
obj* _init_l_nat_digit__char___closed__8() {
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
x_8 = l_nat_digit__char___closed__7;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__9() {
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
x_6 = l_nat_digit__char___closed__8;
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
obj* _init_l_nat_digit__char___closed__10() {
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
obj* _init_l_nat_digit__char___closed__11() {
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
x_8 = l_nat_digit__char___closed__10;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__12() {
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
x_6 = l_nat_digit__char___closed__11;
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
obj* _init_l_nat_digit__char___closed__13() {
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
obj* _init_l_nat_digit__char___closed__14() {
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
x_8 = l_nat_digit__char___closed__13;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__15() {
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
x_6 = l_nat_digit__char___closed__14;
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
obj* _init_l_nat_digit__char___closed__16() {
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
obj* _init_l_nat_digit__char___closed__17() {
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
x_8 = l_nat_digit__char___closed__16;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__18() {
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
x_6 = l_nat_digit__char___closed__17;
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
obj* _init_l_nat_digit__char___closed__19() {
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
obj* _init_l_nat_digit__char___closed__20() {
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
x_8 = l_nat_digit__char___closed__19;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__21() {
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
x_6 = l_nat_digit__char___closed__20;
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
obj* _init_l_nat_digit__char___closed__22() {
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
obj* _init_l_nat_digit__char___closed__23() {
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
x_8 = l_nat_digit__char___closed__22;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__24() {
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
x_6 = l_nat_digit__char___closed__23;
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
obj* _init_l_nat_digit__char___closed__25() {
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
obj* _init_l_nat_digit__char___closed__26() {
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
x_8 = l_nat_digit__char___closed__25;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__27() {
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
x_6 = l_nat_digit__char___closed__26;
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
obj* _init_l_nat_digit__char___closed__28() {
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
obj* _init_l_nat_digit__char___closed__29() {
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
x_8 = l_nat_digit__char___closed__28;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__30() {
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
x_6 = l_nat_digit__char___closed__29;
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
obj* _init_l_nat_digit__char___closed__31() {
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
obj* _init_l_nat_digit__char___closed__32() {
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
x_8 = l_nat_digit__char___closed__31;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__33() {
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
x_6 = l_nat_digit__char___closed__32;
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
obj* _init_l_nat_digit__char___closed__34() {
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
obj* _init_l_nat_digit__char___closed__35() {
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
x_8 = l_nat_digit__char___closed__34;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__36() {
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
x_6 = l_nat_digit__char___closed__35;
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
obj* _init_l_nat_digit__char___closed__37() {
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
obj* _init_l_nat_digit__char___closed__38() {
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
x_8 = l_nat_digit__char___closed__37;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__39() {
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
x_6 = l_nat_digit__char___closed__38;
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
obj* _init_l_nat_digit__char___closed__40() {
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
obj* _init_l_nat_digit__char___closed__41() {
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
x_8 = l_nat_digit__char___closed__40;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__42() {
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
x_6 = l_nat_digit__char___closed__41;
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
obj* _init_l_nat_digit__char___closed__43() {
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
obj* _init_l_nat_digit__char___closed__44() {
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
x_8 = l_nat_digit__char___closed__43;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__45() {
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
x_6 = l_nat_digit__char___closed__44;
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
obj* _init_l_nat_digit__char___closed__46() {
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
obj* _init_l_nat_digit__char___closed__47() {
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
x_8 = l_nat_digit__char___closed__46;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__48() {
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
x_6 = l_nat_digit__char___closed__47;
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
obj* _init_l_nat_digit__char___closed__49() {
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
obj* _init_l_nat_digit__char___closed__50() {
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
x_8 = l_nat_digit__char___closed__49;
lean::inc(x_8);
return x_8;
}
}
}
obj* _init_l_nat_digit__char___closed__51() {
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
x_6 = l_nat_digit__char___closed__50;
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
obj* l_nat_digit__succ___main(obj* x_0, obj* x_1) {
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
lean::dec(x_14);
lean::dec(x_11);
x_20 = l_nat_digit__succ___main(x_0, x_7);
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
obj* l_nat_digit__succ(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_digit__succ___main(x_0, x_1);
return x_2;
}
}
obj* l_nat_to__digits___main(obj* x_0, obj* x_1) {
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
x_11 = l_nat_to__digits___main(x_0, x_7);
x_12 = l_nat_digit__succ___main(x_0, x_11);
return x_12;
}
else
{
obj* x_16; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_16 = l_nat_to__digits___main___closed__1;
lean::inc(x_16);
return x_16;
}
}
}
obj* _init_l_nat_to__digits___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l_nat_to__digits(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_to__digits___main(x_0, x_1);
return x_2;
}
}
obj* l_nat_repr(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::mk_nat_obj(10u);
x_2 = l_nat_to__digits___main(x_1, x_0);
x_3 = l_list_map___main___at_nat_repr___spec__1(x_2);
x_4 = l_list_reverse___rarg(x_3);
x_5 = lean::string_mk(x_4);
return x_5;
}
}
obj* l_list_map___main___at_nat_repr___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
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
x_8 = l_nat_digit__char(x_3);
x_9 = l_list_map___main___at_nat_repr___spec__1(x_5);
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
obj* _init_l_nat_has__repr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repr), 1, 0);
return x_0;
}
}
obj* l_hex__digit__repr(obj* x_0) {
_start:
{
obj* x_1; unsigned x_2; obj* x_4; obj* x_6; 
x_1 = l_nat_digit__char(x_0);
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = lean::string_push(x_4, x_2);
return x_6;
}
}
obj* l_char__to__hex(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::mk_nat_obj(16u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_div(x_2, x_1);
x_4 = lean::nat_mod(x_2, x_1);
lean::dec(x_1);
lean::dec(x_2);
x_7 = l_hex__digit__repr(x_3);
x_8 = l_hex__digit__repr(x_4);
x_9 = lean::string_append(x_7, x_8);
lean::dec(x_8);
return x_9;
}
}
obj* l_char__to__hex___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char__to__hex(x_1);
return x_2;
}
}
obj* l_char_quote__core(unsigned x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
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
lean::dec(x_9);
lean::dec(x_15);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::box_uint32(x_0);
x_21 = lean::nat_dec_eq(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; 
lean::dec(x_21);
x_25 = lean::box(0);
x_7 = x_25;
goto lbl_8;
}
else
{
obj* x_27; 
lean::dec(x_21);
x_27 = l_char_quote__core___closed__5;
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
obj* x_41; 
lean::dec(x_37);
x_41 = lean::box(0);
x_7 = x_41;
goto lbl_8;
}
else
{
obj* x_43; 
lean::dec(x_37);
x_43 = l_char_quote__core___closed__5;
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
obj* x_51; 
lean::dec(x_47);
x_51 = lean::box(0);
x_7 = x_51;
goto lbl_8;
}
else
{
obj* x_53; 
lean::dec(x_47);
x_53 = l_char_quote__core___closed__5;
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
obj* x_61; 
lean::dec(x_57);
x_61 = lean::box(0);
x_7 = x_61;
goto lbl_8;
}
else
{
obj* x_63; 
lean::dec(x_57);
x_63 = l_char_quote__core___closed__5;
lean::inc(x_63);
return x_63;
}
}
lbl_2:
{
obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_1);
x_66 = lean::mk_nat_obj(31u);
x_67 = lean::box_uint32(x_0);
x_68 = lean::nat_dec_le(x_67, x_66);
lean::dec(x_66);
if (lean::obj_tag(x_68) == 0)
{
obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_68);
x_71 = lean::mk_nat_obj(127u);
x_72 = lean::mk_nat_obj(55296u);
x_73 = lean::nat_dec_lt(x_71, x_72);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_76; obj* x_77; 
lean::dec(x_73);
x_76 = lean::mk_nat_obj(57343u);
x_77 = lean::nat_dec_lt(x_76, x_71);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_81; obj* x_82; 
lean::dec(x_71);
lean::dec(x_77);
x_81 = lean::mk_nat_obj(0u);
x_82 = lean::nat_dec_eq(x_67, x_81);
lean::dec(x_81);
lean::dec(x_67);
if (lean::obj_tag(x_82) == 0)
{
obj* x_86; obj* x_88; 
lean::dec(x_82);
x_86 = l_string_join___closed__1;
lean::inc(x_86);
x_88 = lean::string_push(x_86, x_0);
return x_88;
}
else
{
obj* x_90; obj* x_91; obj* x_93; 
lean::dec(x_82);
x_90 = l_char__to__hex(x_0);
x_91 = l_char_quote__core___closed__1;
lean::inc(x_91);
x_93 = lean::string_append(x_91, x_90);
lean::dec(x_90);
return x_93;
}
}
else
{
obj* x_96; obj* x_97; 
lean::dec(x_77);
x_96 = lean::mk_nat_obj(1114112u);
x_97 = lean::nat_dec_lt(x_71, x_96);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_101; obj* x_102; 
lean::dec(x_97);
lean::dec(x_71);
x_101 = lean::mk_nat_obj(0u);
x_102 = lean::nat_dec_eq(x_67, x_101);
lean::dec(x_101);
lean::dec(x_67);
if (lean::obj_tag(x_102) == 0)
{
obj* x_106; obj* x_108; 
lean::dec(x_102);
x_106 = l_string_join___closed__1;
lean::inc(x_106);
x_108 = lean::string_push(x_106, x_0);
return x_108;
}
else
{
obj* x_110; obj* x_111; obj* x_113; 
lean::dec(x_102);
x_110 = l_char__to__hex(x_0);
x_111 = l_char_quote__core___closed__1;
lean::inc(x_111);
x_113 = lean::string_append(x_111, x_110);
lean::dec(x_110);
return x_113;
}
}
else
{
obj* x_116; 
lean::dec(x_97);
x_116 = lean::nat_dec_eq(x_67, x_71);
lean::dec(x_71);
lean::dec(x_67);
if (lean::obj_tag(x_116) == 0)
{
obj* x_120; obj* x_122; 
lean::dec(x_116);
x_120 = l_string_join___closed__1;
lean::inc(x_120);
x_122 = lean::string_push(x_120, x_0);
return x_122;
}
else
{
obj* x_124; obj* x_125; obj* x_127; 
lean::dec(x_116);
x_124 = l_char__to__hex(x_0);
x_125 = l_char_quote__core___closed__1;
lean::inc(x_125);
x_127 = lean::string_append(x_125, x_124);
lean::dec(x_124);
return x_127;
}
}
}
}
else
{
obj* x_130; 
lean::dec(x_73);
x_130 = lean::nat_dec_eq(x_67, x_71);
lean::dec(x_71);
lean::dec(x_67);
if (lean::obj_tag(x_130) == 0)
{
obj* x_134; obj* x_136; 
lean::dec(x_130);
x_134 = l_string_join___closed__1;
lean::inc(x_134);
x_136 = lean::string_push(x_134, x_0);
return x_136;
}
else
{
obj* x_138; obj* x_139; obj* x_141; 
lean::dec(x_130);
x_138 = l_char__to__hex(x_0);
x_139 = l_char_quote__core___closed__1;
lean::inc(x_139);
x_141 = lean::string_append(x_139, x_138);
lean::dec(x_138);
return x_141;
}
}
}
else
{
obj* x_145; obj* x_146; obj* x_148; 
lean::dec(x_68);
lean::dec(x_67);
x_145 = l_char__to__hex(x_0);
x_146 = l_char_quote__core___closed__1;
lean::inc(x_146);
x_148 = lean::string_append(x_146, x_145);
lean::dec(x_145);
return x_148;
}
}
lbl_4:
{
obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_3);
x_151 = lean::mk_nat_obj(34u);
x_152 = lean::mk_nat_obj(55296u);
x_153 = lean::nat_dec_lt(x_151, x_152);
lean::dec(x_152);
if (lean::obj_tag(x_153) == 0)
{
obj* x_156; obj* x_157; 
lean::dec(x_153);
x_156 = lean::mk_nat_obj(57343u);
x_157 = lean::nat_dec_lt(x_156, x_151);
lean::dec(x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_151);
lean::dec(x_157);
x_161 = lean::mk_nat_obj(0u);
x_162 = lean::box_uint32(x_0);
x_163 = lean::nat_dec_eq(x_162, x_161);
lean::dec(x_161);
lean::dec(x_162);
if (lean::obj_tag(x_163) == 0)
{
obj* x_167; 
lean::dec(x_163);
x_167 = lean::box(0);
x_1 = x_167;
goto lbl_2;
}
else
{
obj* x_169; 
lean::dec(x_163);
x_169 = l_char_quote__core___closed__2;
lean::inc(x_169);
return x_169;
}
}
else
{
obj* x_172; obj* x_173; 
lean::dec(x_157);
x_172 = lean::mk_nat_obj(1114112u);
x_173 = lean::nat_dec_lt(x_151, x_172);
lean::dec(x_172);
if (lean::obj_tag(x_173) == 0)
{
obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_173);
lean::dec(x_151);
x_177 = lean::mk_nat_obj(0u);
x_178 = lean::box_uint32(x_0);
x_179 = lean::nat_dec_eq(x_178, x_177);
lean::dec(x_177);
lean::dec(x_178);
if (lean::obj_tag(x_179) == 0)
{
obj* x_183; 
lean::dec(x_179);
x_183 = lean::box(0);
x_1 = x_183;
goto lbl_2;
}
else
{
obj* x_185; 
lean::dec(x_179);
x_185 = l_char_quote__core___closed__2;
lean::inc(x_185);
return x_185;
}
}
else
{
obj* x_188; obj* x_189; 
lean::dec(x_173);
x_188 = lean::box_uint32(x_0);
x_189 = lean::nat_dec_eq(x_188, x_151);
lean::dec(x_151);
lean::dec(x_188);
if (lean::obj_tag(x_189) == 0)
{
obj* x_193; 
lean::dec(x_189);
x_193 = lean::box(0);
x_1 = x_193;
goto lbl_2;
}
else
{
obj* x_195; 
lean::dec(x_189);
x_195 = l_char_quote__core___closed__2;
lean::inc(x_195);
return x_195;
}
}
}
}
else
{
obj* x_198; obj* x_199; 
lean::dec(x_153);
x_198 = lean::box_uint32(x_0);
x_199 = lean::nat_dec_eq(x_198, x_151);
lean::dec(x_151);
lean::dec(x_198);
if (lean::obj_tag(x_199) == 0)
{
obj* x_203; 
lean::dec(x_199);
x_203 = lean::box(0);
x_1 = x_203;
goto lbl_2;
}
else
{
obj* x_205; 
lean::dec(x_199);
x_205 = l_char_quote__core___closed__2;
lean::inc(x_205);
return x_205;
}
}
}
lbl_6:
{
obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_5);
x_208 = lean::mk_nat_obj(92u);
x_209 = lean::mk_nat_obj(55296u);
x_210 = lean::nat_dec_lt(x_208, x_209);
lean::dec(x_209);
if (lean::obj_tag(x_210) == 0)
{
obj* x_213; obj* x_214; 
lean::dec(x_210);
x_213 = lean::mk_nat_obj(57343u);
x_214 = lean::nat_dec_lt(x_213, x_208);
lean::dec(x_213);
if (lean::obj_tag(x_214) == 0)
{
obj* x_218; obj* x_219; obj* x_220; 
lean::dec(x_208);
lean::dec(x_214);
x_218 = lean::mk_nat_obj(0u);
x_219 = lean::box_uint32(x_0);
x_220 = lean::nat_dec_eq(x_219, x_218);
lean::dec(x_218);
lean::dec(x_219);
if (lean::obj_tag(x_220) == 0)
{
obj* x_224; 
lean::dec(x_220);
x_224 = lean::box(0);
x_3 = x_224;
goto lbl_4;
}
else
{
obj* x_226; 
lean::dec(x_220);
x_226 = l_char_quote__core___closed__3;
lean::inc(x_226);
return x_226;
}
}
else
{
obj* x_229; obj* x_230; 
lean::dec(x_214);
x_229 = lean::mk_nat_obj(1114112u);
x_230 = lean::nat_dec_lt(x_208, x_229);
lean::dec(x_229);
if (lean::obj_tag(x_230) == 0)
{
obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_208);
lean::dec(x_230);
x_234 = lean::mk_nat_obj(0u);
x_235 = lean::box_uint32(x_0);
x_236 = lean::nat_dec_eq(x_235, x_234);
lean::dec(x_234);
lean::dec(x_235);
if (lean::obj_tag(x_236) == 0)
{
obj* x_240; 
lean::dec(x_236);
x_240 = lean::box(0);
x_3 = x_240;
goto lbl_4;
}
else
{
obj* x_242; 
lean::dec(x_236);
x_242 = l_char_quote__core___closed__3;
lean::inc(x_242);
return x_242;
}
}
else
{
obj* x_245; obj* x_246; 
lean::dec(x_230);
x_245 = lean::box_uint32(x_0);
x_246 = lean::nat_dec_eq(x_245, x_208);
lean::dec(x_208);
lean::dec(x_245);
if (lean::obj_tag(x_246) == 0)
{
obj* x_250; 
lean::dec(x_246);
x_250 = lean::box(0);
x_3 = x_250;
goto lbl_4;
}
else
{
obj* x_252; 
lean::dec(x_246);
x_252 = l_char_quote__core___closed__3;
lean::inc(x_252);
return x_252;
}
}
}
}
else
{
obj* x_255; obj* x_256; 
lean::dec(x_210);
x_255 = lean::box_uint32(x_0);
x_256 = lean::nat_dec_eq(x_255, x_208);
lean::dec(x_208);
lean::dec(x_255);
if (lean::obj_tag(x_256) == 0)
{
obj* x_260; 
lean::dec(x_256);
x_260 = lean::box(0);
x_3 = x_260;
goto lbl_4;
}
else
{
obj* x_262; 
lean::dec(x_256);
x_262 = l_char_quote__core___closed__3;
lean::inc(x_262);
return x_262;
}
}
}
lbl_8:
{
obj* x_265; obj* x_266; obj* x_267; 
lean::dec(x_7);
x_265 = lean::mk_nat_obj(9u);
x_266 = lean::mk_nat_obj(55296u);
x_267 = lean::nat_dec_lt(x_265, x_266);
lean::dec(x_266);
if (lean::obj_tag(x_267) == 0)
{
obj* x_270; obj* x_271; 
lean::dec(x_267);
x_270 = lean::mk_nat_obj(57343u);
x_271 = lean::nat_dec_lt(x_270, x_265);
lean::dec(x_270);
if (lean::obj_tag(x_271) == 0)
{
obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_271);
lean::dec(x_265);
x_275 = lean::mk_nat_obj(0u);
x_276 = lean::box_uint32(x_0);
x_277 = lean::nat_dec_eq(x_276, x_275);
lean::dec(x_275);
lean::dec(x_276);
if (lean::obj_tag(x_277) == 0)
{
obj* x_281; 
lean::dec(x_277);
x_281 = lean::box(0);
x_5 = x_281;
goto lbl_6;
}
else
{
obj* x_283; 
lean::dec(x_277);
x_283 = l_char_quote__core___closed__4;
lean::inc(x_283);
return x_283;
}
}
else
{
obj* x_286; obj* x_287; 
lean::dec(x_271);
x_286 = lean::mk_nat_obj(1114112u);
x_287 = lean::nat_dec_lt(x_265, x_286);
lean::dec(x_286);
if (lean::obj_tag(x_287) == 0)
{
obj* x_291; obj* x_292; obj* x_293; 
lean::dec(x_287);
lean::dec(x_265);
x_291 = lean::mk_nat_obj(0u);
x_292 = lean::box_uint32(x_0);
x_293 = lean::nat_dec_eq(x_292, x_291);
lean::dec(x_291);
lean::dec(x_292);
if (lean::obj_tag(x_293) == 0)
{
obj* x_297; 
lean::dec(x_293);
x_297 = lean::box(0);
x_5 = x_297;
goto lbl_6;
}
else
{
obj* x_299; 
lean::dec(x_293);
x_299 = l_char_quote__core___closed__4;
lean::inc(x_299);
return x_299;
}
}
else
{
obj* x_302; obj* x_303; 
lean::dec(x_287);
x_302 = lean::box_uint32(x_0);
x_303 = lean::nat_dec_eq(x_302, x_265);
lean::dec(x_265);
lean::dec(x_302);
if (lean::obj_tag(x_303) == 0)
{
obj* x_307; 
lean::dec(x_303);
x_307 = lean::box(0);
x_5 = x_307;
goto lbl_6;
}
else
{
obj* x_309; 
lean::dec(x_303);
x_309 = l_char_quote__core___closed__4;
lean::inc(x_309);
return x_309;
}
}
}
}
else
{
obj* x_312; obj* x_313; 
lean::dec(x_267);
x_312 = lean::box_uint32(x_0);
x_313 = lean::nat_dec_eq(x_312, x_265);
lean::dec(x_265);
lean::dec(x_312);
if (lean::obj_tag(x_313) == 0)
{
obj* x_317; 
lean::dec(x_313);
x_317 = lean::box(0);
x_5 = x_317;
goto lbl_6;
}
else
{
obj* x_319; 
lean::dec(x_313);
x_319 = l_char_quote__core___closed__4;
lean::inc(x_319);
return x_319;
}
}
}
}
}
obj* _init_l_char_quote__core___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\x");
return x_0;
}
}
obj* _init_l_char_quote__core___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\\"");
return x_0;
}
}
obj* _init_l_char_quote__core___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\\\");
return x_0;
}
}
obj* _init_l_char_quote__core___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\t");
return x_0;
}
}
obj* _init_l_char_quote__core___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\\n");
return x_0;
}
}
obj* l_char_quote__core___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_quote__core(x_1);
return x_2;
}
}
obj* l_char_has__repr(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; 
x_1 = l_char_quote__core(x_0);
x_2 = l_char_has__repr___closed__1;
lean::inc(x_2);
x_4 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_6 = lean::string_append(x_4, x_2);
return x_6;
}
}
obj* _init_l_char_has__repr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("'");
return x_0;
}
}
obj* l_char_has__repr___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_has__repr(x_1);
return x_2;
}
}
obj* l_string_quote__aux___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_string_join___closed__1;
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
x_11 = l_char_quote__core(x_9);
x_12 = l_string_quote__aux___main(x_6);
x_13 = lean::string_append(x_11, x_12);
lean::dec(x_12);
return x_13;
}
}
}
obj* l_string_quote__aux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_quote__aux___main(x_0);
return x_1;
}
}
obj* l_string_quote(obj* x_0) {
_start:
{
unsigned char x_2; 
lean::inc(x_0);
x_2 = l_string_is__empty(x_0);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_3 = lean::string_data(x_0);
x_4 = l_string_quote__aux___main(x_3);
x_5 = l_string_quote___closed__1;
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
x_11 = l_string_quote___closed__2;
lean::inc(x_11);
return x_11;
}
}
}
obj* _init_l_string_quote___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\"");
return x_0;
}
}
obj* _init_l_string_quote___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\"\"");
return x_0;
}
}
obj* _init_l_string_has__repr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_quote), 1, 0);
return x_0;
}
}
obj* l_string_iterator_has__repr(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
x_3 = l_string_quote(x_1);
x_4 = l_string_iterator_has__repr___closed__1;
x_5 = lean::string_append(x_3, x_4);
return x_5;
}
}
obj* _init_l_string_iterator_has__repr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(".mk_iterator");
return x_0;
}
}
obj* l_fin_has__repr___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_nat_repr(x_0);
return x_1;
}
}
obj* l_fin_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_has__repr___rarg), 1, 0);
return x_2;
}
}
obj* l_uint16_has__repr(unsigned short x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint16_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint16_has__repr___boxed(obj* x_0) {
_start:
{
unsigned short x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_uint16_has__repr(x_1);
return x_2;
}
}
obj* l_uint32_has__repr(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint32_has__repr___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_uint32_has__repr(x_1);
return x_2;
}
}
obj* l_uint64_has__repr(unsigned long long x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint64_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint64_has__repr___boxed(obj* x_0) {
_start:
{
unsigned long long x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = l_uint64_has__repr(x_1);
return x_2;
}
}
obj* l_usize_has__repr(size_t x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::usize_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_usize_has__repr___boxed(obj* x_0) {
_start:
{
size_t x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = l_usize_has__repr(x_1);
return x_2;
}
}
obj* l_char_repr(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; 
x_1 = l_char_quote__core(x_0);
x_2 = l_char_has__repr___closed__1;
lean::inc(x_2);
x_4 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_6 = lean::string_append(x_4, x_2);
return x_6;
}
}
obj* l_char_repr___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_repr(x_1);
return x_2;
}
}
void initialize_init_data_string_basic();
void initialize_init_data_uint();
void initialize_init_data_usize();
void initialize_init_data_nat_div();
static bool _G_initialized = false;
void initialize_init_data_repr() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_string_basic();
 initialize_init_data_uint();
 initialize_init_data_usize();
 initialize_init_data_nat_div();
 l_bool_has__repr___closed__1 = _init_l_bool_has__repr___closed__1();
 l_bool_has__repr___closed__2 = _init_l_bool_has__repr___closed__2();
 l_list_repr__aux___main___rarg___closed__1 = _init_l_list_repr__aux___main___rarg___closed__1();
 l_list_repr___main___rarg___closed__1 = _init_l_list_repr___main___rarg___closed__1();
 l_list_repr___main___rarg___closed__2 = _init_l_list_repr___main___rarg___closed__2();
 l_list_repr___main___rarg___closed__3 = _init_l_list_repr___main___rarg___closed__3();
 l_unit_has__repr___closed__1 = _init_l_unit_has__repr___closed__1();
 l_option_has__repr___rarg___closed__1 = _init_l_option_has__repr___rarg___closed__1();
 l_option_has__repr___rarg___closed__2 = _init_l_option_has__repr___rarg___closed__2();
 l_option_has__repr___rarg___closed__3 = _init_l_option_has__repr___rarg___closed__3();
 l_sum_has__repr___rarg___closed__1 = _init_l_sum_has__repr___rarg___closed__1();
 l_sum_has__repr___rarg___closed__2 = _init_l_sum_has__repr___rarg___closed__2();
 l_prod_has__repr___rarg___closed__1 = _init_l_prod_has__repr___rarg___closed__1();
 l_sigma_has__repr___rarg___closed__1 = _init_l_sigma_has__repr___rarg___closed__1();
 l_sigma_has__repr___rarg___closed__2 = _init_l_sigma_has__repr___rarg___closed__2();
 l_nat_digit__char___closed__1 = _init_l_nat_digit__char___closed__1();
 l_nat_digit__char___closed__2 = _init_l_nat_digit__char___closed__2();
 l_nat_digit__char___closed__3 = _init_l_nat_digit__char___closed__3();
 l_nat_digit__char___closed__4 = _init_l_nat_digit__char___closed__4();
 l_nat_digit__char___closed__5 = _init_l_nat_digit__char___closed__5();
 l_nat_digit__char___closed__6 = _init_l_nat_digit__char___closed__6();
 l_nat_digit__char___closed__7 = _init_l_nat_digit__char___closed__7();
 l_nat_digit__char___closed__8 = _init_l_nat_digit__char___closed__8();
 l_nat_digit__char___closed__9 = _init_l_nat_digit__char___closed__9();
 l_nat_digit__char___closed__10 = _init_l_nat_digit__char___closed__10();
 l_nat_digit__char___closed__11 = _init_l_nat_digit__char___closed__11();
 l_nat_digit__char___closed__12 = _init_l_nat_digit__char___closed__12();
 l_nat_digit__char___closed__13 = _init_l_nat_digit__char___closed__13();
 l_nat_digit__char___closed__14 = _init_l_nat_digit__char___closed__14();
 l_nat_digit__char___closed__15 = _init_l_nat_digit__char___closed__15();
 l_nat_digit__char___closed__16 = _init_l_nat_digit__char___closed__16();
 l_nat_digit__char___closed__17 = _init_l_nat_digit__char___closed__17();
 l_nat_digit__char___closed__18 = _init_l_nat_digit__char___closed__18();
 l_nat_digit__char___closed__19 = _init_l_nat_digit__char___closed__19();
 l_nat_digit__char___closed__20 = _init_l_nat_digit__char___closed__20();
 l_nat_digit__char___closed__21 = _init_l_nat_digit__char___closed__21();
 l_nat_digit__char___closed__22 = _init_l_nat_digit__char___closed__22();
 l_nat_digit__char___closed__23 = _init_l_nat_digit__char___closed__23();
 l_nat_digit__char___closed__24 = _init_l_nat_digit__char___closed__24();
 l_nat_digit__char___closed__25 = _init_l_nat_digit__char___closed__25();
 l_nat_digit__char___closed__26 = _init_l_nat_digit__char___closed__26();
 l_nat_digit__char___closed__27 = _init_l_nat_digit__char___closed__27();
 l_nat_digit__char___closed__28 = _init_l_nat_digit__char___closed__28();
 l_nat_digit__char___closed__29 = _init_l_nat_digit__char___closed__29();
 l_nat_digit__char___closed__30 = _init_l_nat_digit__char___closed__30();
 l_nat_digit__char___closed__31 = _init_l_nat_digit__char___closed__31();
 l_nat_digit__char___closed__32 = _init_l_nat_digit__char___closed__32();
 l_nat_digit__char___closed__33 = _init_l_nat_digit__char___closed__33();
 l_nat_digit__char___closed__34 = _init_l_nat_digit__char___closed__34();
 l_nat_digit__char___closed__35 = _init_l_nat_digit__char___closed__35();
 l_nat_digit__char___closed__36 = _init_l_nat_digit__char___closed__36();
 l_nat_digit__char___closed__37 = _init_l_nat_digit__char___closed__37();
 l_nat_digit__char___closed__38 = _init_l_nat_digit__char___closed__38();
 l_nat_digit__char___closed__39 = _init_l_nat_digit__char___closed__39();
 l_nat_digit__char___closed__40 = _init_l_nat_digit__char___closed__40();
 l_nat_digit__char___closed__41 = _init_l_nat_digit__char___closed__41();
 l_nat_digit__char___closed__42 = _init_l_nat_digit__char___closed__42();
 l_nat_digit__char___closed__43 = _init_l_nat_digit__char___closed__43();
 l_nat_digit__char___closed__44 = _init_l_nat_digit__char___closed__44();
 l_nat_digit__char___closed__45 = _init_l_nat_digit__char___closed__45();
 l_nat_digit__char___closed__46 = _init_l_nat_digit__char___closed__46();
 l_nat_digit__char___closed__47 = _init_l_nat_digit__char___closed__47();
 l_nat_digit__char___closed__48 = _init_l_nat_digit__char___closed__48();
 l_nat_digit__char___closed__49 = _init_l_nat_digit__char___closed__49();
 l_nat_digit__char___closed__50 = _init_l_nat_digit__char___closed__50();
 l_nat_digit__char___closed__51 = _init_l_nat_digit__char___closed__51();
 l_nat_to__digits___main___closed__1 = _init_l_nat_to__digits___main___closed__1();
 l_nat_has__repr = _init_l_nat_has__repr();
 l_char_quote__core___closed__1 = _init_l_char_quote__core___closed__1();
 l_char_quote__core___closed__2 = _init_l_char_quote__core___closed__2();
 l_char_quote__core___closed__3 = _init_l_char_quote__core___closed__3();
 l_char_quote__core___closed__4 = _init_l_char_quote__core___closed__4();
 l_char_quote__core___closed__5 = _init_l_char_quote__core___closed__5();
 l_char_has__repr___closed__1 = _init_l_char_has__repr___closed__1();
 l_string_quote___closed__1 = _init_l_string_quote___closed__1();
 l_string_quote___closed__2 = _init_l_string_quote___closed__2();
 l_string_has__repr = _init_l_string_has__repr();
 l_string_iterator_has__repr___closed__1 = _init_l_string_iterator_has__repr___closed__1();
}

// Lean compiler output
// Module: init.data.to_string
// Imports: init.data.string.basic init.data.uint init.data.nat.div init.data.repr
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
obj* _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(obj*, unsigned char, obj*);
obj* _l_s6_uint16_s15_has__to__string_s7___boxed(obj*);
obj* _l_s4_list_s15_has__to__string(obj*);
obj* _l_s6_uint16_s15_has__to__string(unsigned short);
obj* _l_s3_fin_s15_has__to__string(obj*);
obj* _l_s6_uint32_s15_has__to__string(unsigned);
obj* _l_s4_list_s10_to__string_s6___main(obj*);
obj* _l_s6_option_s15_has__to__string(obj*);
obj* _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s2_id_s15_has__to__string_s6___rarg(obj*);
obj* _l_s4_unit_s9_has__repr_s11___closed__1;
obj* _l_s6_uint64_s15_has__to__string_s7___boxed(obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__2;
obj* _l_s4_list_s15_to__string__aux_s6___main(obj*);
obj* _l_s6_string_s8_iterator_s15_has__to__string(obj*);
obj* _l_s4_unit_s15_has__to__string_s7___boxed(obj*);
obj* _l_s4_list_s15_to__string__aux_s6___rarg(obj*, unsigned char, obj*);
obj* _l_s4_unit_s15_has__to__string(unsigned char);
obj* _l_s4_list_s15_has__to__string_s6___rarg(obj*);
obj* _l_s4_list_s15_to__string__aux_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s5_sigma_s15_has__to__string_s6___rarg(obj*, obj*, obj*);
obj* _l_s7_subtype_s15_has__to__string_s6___rarg(obj*, obj*);
obj* _l_s9_decidable_s15_has__to__string_s6___rarg(obj*);
obj* _l_s6_uint32_s7_to__nat_s6___main(unsigned);
obj* _l_s4_list_s15_to__string__aux(obj*);
obj* _l_s4_prod_s15_has__to__string(obj*, obj*);
obj* _l_s6_uint16_s7_to__nat_s6___main(unsigned short);
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
obj* _l_s4_char_s15_has__to__string_s7___boxed(obj*);
obj* _l_s9_decidable_s15_has__to__string(obj*);
obj* _l_s4_bool_s15_has__to__string(unsigned char);
obj* _l_s4_bool_s15_has__to__string_s7___boxed(obj*);
obj* _l_s4_list_s10_to__string_s6___main_s6___rarg(obj*, obj*);
obj* _l_s6_uint64_s7_to__nat_s6___main(unsigned long long);
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
obj* _l_s5_usize_s15_has__to__string(size_t);
obj* _l_s3_sum_s9_has__repr_s6___rarg_s11___closed__2;
obj* _l_s4_bool_s9_has__repr_s11___closed__1;
obj* _l_s3_sum_s15_has__to__string(obj*, obj*);
obj* _l_s3_sum_s15_has__to__string_s6___rarg(obj*, obj*, obj*);
obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s4_prod_s15_has__to__string_s6___rarg(obj*, obj*, obj*);
obj* _l_s6_option_s15_has__to__string_s6___rarg(obj*, obj*);
obj* _l_s3_nat_s15_has__to__string(obj*);
obj* _l_s2_id_s15_has__to__string(obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__1;
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__2;
obj* _l_s4_list_s10_to__string(obj*);
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_list_s10_to__string_s6___rarg(obj*, obj*);
obj* _l_s6_uint32_s15_has__to__string_s7___boxed(obj*);
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
obj* _l_s4_bool_s9_has__repr_s11___closed__2;
obj* _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s5_sigma_s9_has__repr_s6___rarg_s11___closed__2;
obj* _l_s4_list_s15_to__string__aux_s6___main_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s6_string_s15_has__to__string(obj*);
obj* _l_s7_subtype_s15_has__to__string(obj*, obj*);
obj* _l_s4_char_s15_has__to__string(unsigned);
obj* _l_s5_usize_s7_to__nat_s6___main(size_t);
obj* _l_s5_usize_s15_has__to__string_s7___boxed(obj*);
obj* _l_s5_sigma_s15_has__to__string(obj*, obj*);
obj* _l_s6_uint64_s15_has__to__string(unsigned long long);
obj* _l_s3_fin_s15_has__to__string_s6___rarg(obj*);
obj* _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s2_id_s15_has__to__string_s6___rarg(obj* x_0) {
{
return x_0;
}
}
obj* _l_s2_id_s15_has__to__string(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s15_has__to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s6_string_s15_has__to__string(obj* x_0) {
{
return x_0;
}
}
obj* _l_s6_string_s8_iterator_s15_has__to__string(obj* x_0) {
{
obj* x_1;
x_1 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s4_bool_s15_has__to__string(unsigned char x_0) {
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
obj* _l_s4_bool_s15_has__to__string_s7___boxed(obj* x_0) {
{
unsigned char x_1;
obj* x_2;
x_1 = lean::unbox(x_0);
x_2 = _l_s4_bool_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s9_decidable_s15_has__to__string_s6___rarg(obj* x_0) {
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
obj* _l_s9_decidable_s15_has__to__string(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_decidable_s15_has__to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
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
obj* x_7;
obj* x_9;
obj* x_13;
obj* x_14;
obj* x_16;
obj* x_18;
obj* x_19;
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
x_18 = _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(x_0, x_1, x_9);
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
obj* x_25;
obj* x_27;
obj* x_31;
unsigned char x_32;
obj* x_33;
obj* x_34;
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_2, 1);
lean::inc(x_27);
lean::dec(x_2);
lean::inc(x_0);
x_31 = lean::apply_1(x_0, x_25);
x_32 = 0;
x_33 = _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(x_0, x_32, x_27);
x_34 = lean::string_append(x_31, x_33);
lean::dec(x_33);
return x_34;
}
}
}
}
obj* _l_s4_list_s15_to__string__aux_s6___main(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s15_to__string__aux_s6___main_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s15_to__string__aux_s6___main_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3;
obj* x_4;
x_3 = lean::unbox(x_1);
x_4 = _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_list_s15_to__string__aux_s6___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
{
obj* x_3;
x_3 = _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_list_s15_to__string__aux(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s15_to__string__aux_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s15_to__string__aux_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3;
obj* x_4;
x_3 = lean::unbox(x_1);
x_4 = _l_s4_list_s15_to__string__aux_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_list_s10_to__string_s6___main_s6___rarg(obj* x_0, obj* x_1) {
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
unsigned char x_6;
obj* x_7;
obj* x_8;
obj* x_10;
obj* x_12;
obj* x_13;
x_6 = 1;
x_7 = _l_s4_list_s15_to__string__aux_s6___main_s6___rarg(x_0, x_6, x_1);
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
obj* _l_s4_list_s10_to__string_s6___main(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s10_to__string_s6___main_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_list_s10_to__string_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = _l_s4_list_s10_to__string_s6___main_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_list_s10_to__string(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s10_to__string_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_list_s15_has__to__string_s6___rarg(obj* x_0) {
{
obj* x_1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s10_to__string_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_list_s15_has__to__string(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s15_has__to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_unit_s15_has__to__string(unsigned char x_0) {
{
obj* x_1;
x_1 = _l_s4_unit_s9_has__repr_s11___closed__1;
lean::inc(x_1);
return x_1;
}
}
obj* _l_s4_unit_s15_has__to__string_s7___boxed(obj* x_0) {
{
unsigned char x_1;
obj* x_2;
x_1 = lean::unbox(x_0);
x_2 = _l_s4_unit_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s3_nat_s15_has__to__string(obj* x_0) {
{
obj* x_1;
x_1 = _l_s3_nat_s4_repr(x_0);
return x_1;
}
}
obj* _l_s4_char_s15_has__to__string(unsigned x_0) {
{
obj* x_1;
obj* x_3;
x_1 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_1);
x_3 = lean::string_push(x_1, x_0);
return x_3;
}
}
obj* _l_s4_char_s15_has__to__string_s7___boxed(obj* x_0) {
{
unsigned x_1;
obj* x_2;
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_char_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s3_fin_s15_has__to__string_s6___rarg(obj* x_0) {
{
obj* x_1;
x_1 = _l_s3_nat_s4_repr(x_0);
return x_1;
}
}
obj* _l_s3_fin_s15_has__to__string(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_fin_s15_has__to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s6_uint16_s15_has__to__string(unsigned short x_0) {
{
obj* x_1;
obj* x_2;
x_1 = _l_s6_uint16_s7_to__nat_s6___main(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s6_uint16_s15_has__to__string_s7___boxed(obj* x_0) {
{
unsigned short x_1;
obj* x_2;
x_1 = lean::unbox(x_0);
x_2 = _l_s6_uint16_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s6_uint32_s15_has__to__string(unsigned x_0) {
{
obj* x_1;
obj* x_2;
x_1 = _l_s6_uint32_s7_to__nat_s6___main(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s6_uint32_s15_has__to__string_s7___boxed(obj* x_0) {
{
unsigned x_1;
obj* x_2;
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s6_uint32_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s6_uint64_s15_has__to__string(unsigned long long x_0) {
{
obj* x_1;
obj* x_2;
x_1 = _l_s6_uint64_s7_to__nat_s6___main(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s6_uint64_s15_has__to__string_s7___boxed(obj* x_0) {
{
unsigned long long x_1;
obj* x_2;
x_1 = lean::unbox_uint64(x_0);
x_2 = _l_s6_uint64_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s5_usize_s15_has__to__string(size_t x_0) {
{
obj* x_1;
obj* x_2;
x_1 = _l_s5_usize_s7_to__nat_s6___main(x_0);
x_2 = _l_s3_nat_s4_repr(x_1);
return x_2;
}
}
obj* _l_s5_usize_s15_has__to__string_s7___boxed(obj* x_0) {
{
size_t x_1;
obj* x_2;
x_1 = lean::unbox_size_t(x_0);
x_2 = _l_s5_usize_s15_has__to__string(x_1);
return x_2;
}
}
obj* _l_s6_option_s15_has__to__string_s6___rarg(obj* x_0, obj* x_1) {
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
obj* x_6;
obj* x_9;
obj* x_10;
obj* x_12;
obj* x_14;
obj* x_15;
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
obj* _l_s6_option_s15_has__to__string(obj* x_0) {
{
obj* x_2;
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_option_s15_has__to__string_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s3_sum_s15_has__to__string_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4;
obj* x_7;
obj* x_8;
obj* x_10;
obj* x_12;
obj* x_13;
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
obj* x_15;
obj* x_18;
obj* x_19;
obj* x_21;
obj* x_23;
obj* x_24;
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
obj* _l_s3_sum_s15_has__to__string(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_sum_s15_has__to__string_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_prod_s15_has__to__string_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_5;
obj* x_8;
obj* x_9;
obj* x_11;
obj* x_13;
obj* x_14;
obj* x_15;
obj* x_16;
obj* x_18;
obj* x_19;
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
obj* _l_s4_prod_s15_has__to__string(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_prod_s15_has__to__string_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s5_sigma_s15_has__to__string_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_5;
obj* x_9;
obj* x_10;
obj* x_12;
obj* x_14;
obj* x_15;
obj* x_16;
obj* x_17;
obj* x_19;
obj* x_20;
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
obj* _l_s5_sigma_s15_has__to__string(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_sigma_s15_has__to__string_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s7_subtype_s15_has__to__string_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _l_s7_subtype_s15_has__to__string(obj* x_0, obj* x_1) {
{
obj* x_4;
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_subtype_s15_has__to__string_s6___rarg), 2, 0);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
void _l_initialize__l_s4_init_s4_data_s4_uint();
void _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
void _l_initialize__l_s4_init_s4_data_s4_repr();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s10_to__string() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_initialize__l_s4_init_s4_data_s4_uint();
 _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
 _l_initialize__l_s4_init_s4_data_s4_repr();
}

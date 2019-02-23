// Lean compiler output
// Module: init.data.repr
// Imports: init.data.string.basic init.data.uint init.data.usize init.data.nat.div
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
obj* l_usize_has__repr(usize);
uint32 l_nat_digit__char(obj*);
obj* l_decidable_has__repr___boxed(obj*);
obj* l_unit_has__repr___boxed(obj*);
obj* l_list_repr___main___rarg(obj*, obj*);
obj* l_string_quote__aux(obj*);
obj* l_string_iterator_has__repr___closed__1;
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_option_has__repr___rarg___closed__2;
obj* l_id_has__repr___rarg(obj*);
obj* l_option_has__repr___boxed(obj*);
obj* l_string_has__repr;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_fin_has__repr(obj*);
obj* l_list_repr__aux___rarg___boxed(obj*, obj*, obj*);
obj* l_uint32_has__repr(uint32);
obj* l_unit_has__repr___closed__1;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_list_repr__aux___main(obj*);
obj* l_string_quote__aux___main___boxed(obj*);
obj* l_char_quote__core___boxed(obj*);
obj* l_uint16_has__repr(uint16);
obj* l_list_repr__aux___boxed(obj*);
obj* l_fin_has__repr___rarg(obj*);
obj* l_nat_has__repr;
obj* l_char_repr(uint32);
obj* l_nat_to__digits__core___boxed(obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
obj* l_sum_has__repr___rarg___closed__1;
obj* l_option_has__repr___rarg___closed__1;
obj* l_id_has__repr(obj*);
obj* l_nat_to__digits__core(obj*, obj*, obj*, obj*);
uint8 l_string_is__empty(obj*);
obj* l_nat_digit__char___boxed(obj*);
obj* l_list_repr___main___rarg___closed__1;
obj* l_option_has__repr(obj*);
obj* l_hex__digit__repr(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_char_quote__core___closed__2;
obj* l_sum_has__repr___boxed(obj*, obj*);
obj* l_usize_has__repr___boxed(obj*);
obj* l_string_quote__aux___main(obj*);
obj* l_char_quote__core___closed__1;
obj* l_bool_has__repr___boxed(obj*);
obj* l_nat_to__digits(obj*, obj*);
obj* l_sigma_has__repr(obj*, obj*);
obj* l_sum_has__repr___rarg___closed__2;
obj* l_string_iterator_has__repr___boxed(obj*);
obj* l_sum_has__repr(obj*, obj*);
obj* l_char_quote__core___closed__4;
namespace lean {
obj* string_data(obj*);
}
obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_char_has__repr___boxed(obj*);
obj* l_char_quote__core___closed__5;
obj* l_string_iterator_has__repr(obj*);
obj* l_list_repr___main___rarg___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
obj* string_iterator_remaining_to_string(obj*);
}
obj* l_char_has__repr___closed__1;
obj* l_decidable_has__repr(obj*);
obj* l_string_quote___closed__1;
obj* l_bool_has__repr(uint8);
obj* l_list_repr___rarg(obj*, obj*);
obj* l_subtype_has__repr___boxed(obj*, obj*);
extern obj* l_string_join___closed__1;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_list_has__repr(obj*);
obj* l_char__to__hex___boxed(obj*);
obj* l_decidable_has__repr___rarg___boxed(obj*);
obj* l_sigma_has__repr___rarg___closed__1;
obj* l_list_has__repr___boxed(obj*);
obj* l_uint64_has__repr(uint64);
obj* l_string_quote___closed__2;
namespace lean {
obj* string_mk(obj*);
}
obj* l_list_repr__aux___main___rarg___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_char_quote__core___closed__3;
obj* l_char_repr___boxed(obj*);
obj* l_char_has__repr(uint32);
obj* l_list_has__repr___rarg(obj*);
obj* l_option_has__repr___rarg(obj*, obj*);
obj* l_list_repr___main___rarg___closed__2;
obj* l_fin_has__repr___boxed(obj*);
obj* l_list_repr__aux(obj*);
obj* l_bool_has__repr___closed__2;
obj* l_prod_has__repr___rarg___closed__1;
obj* l_nat_to__digits___boxed(obj*, obj*);
obj* l_sigma_has__repr___rarg(obj*, obj*, obj*);
obj* l_uint32_has__repr___boxed(obj*);
obj* l_uint64_has__repr___boxed(obj*);
obj* l_subtype_has__repr___rarg(obj*, obj*);
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_sigma_has__repr___boxed(obj*, obj*);
obj* l_hex__digit__repr___boxed(obj*);
obj* l_decidable_has__repr___rarg(uint8);
obj* l_sum_has__repr___rarg(obj*, obj*, obj*);
obj* l_bool_has__repr___closed__1;
obj* l_prod_has__repr(obj*, obj*);
obj* l_list_repr(obj*);
obj* l_subtype_has__repr(obj*, obj*);
obj* l_list_repr___main(obj*);
obj* l_string_quote__aux___boxed(obj*);
obj* l_nat_repr(obj*);
obj* l_prod_has__repr___rarg(obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_sigma_has__repr___rarg___closed__2;
obj* l_list_repr__aux___main___boxed(obj*);
obj* l_prod_has__repr___boxed(obj*, obj*);
obj* l_id_has__repr___boxed(obj*);
obj* l_list_repr___boxed(obj*);
obj* l_char__to__hex(uint32);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_nat_to__digits__core___main___boxed(obj*, obj*, obj*, obj*);
obj* l_option_has__repr___rarg___closed__3;
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_nat_to__digits__core___main(obj*, obj*, obj*, obj*);
obj* l_list_repr___main___boxed(obj*);
obj* l_unit_has__repr(obj*);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_char_quote__core(uint32);
obj* l_list_repr__aux___main___rarg(obj*, uint8, obj*);
obj* l_id_has__repr___rarg___boxed(obj*);
obj* l_uint16_has__repr___boxed(obj*);
obj* l_list_repr__aux___rarg(obj*, uint8, obj*);
obj* l_id_has__repr___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_id_has__repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_has__repr___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_id_has__repr___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_id_has__repr___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_id_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_id_has__repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_bool_has__repr(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
obj* x_1; 
x_1 = l_bool_has__repr___closed__1;
return x_1;
}
else
{
obj* x_2; 
x_2 = l_bool_has__repr___closed__2;
return x_2;
}
}
}
obj* l_bool_has__repr___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_bool_has__repr(x_1);
return x_2;
}
}
obj* l_decidable_has__repr___rarg(uint8 x_0) {
_start:
{
if (x_0 == 0)
{
obj* x_1; 
x_1 = l_bool_has__repr___closed__1;
return x_1;
}
else
{
obj* x_2; 
x_2 = l_bool_has__repr___closed__2;
return x_2;
}
}
}
obj* l_decidable_has__repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_has__repr___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_decidable_has__repr___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_decidable_has__repr___rarg(x_1);
return x_2;
}
}
obj* l_decidable_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_decidable_has__repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_list_repr__aux___main___rarg(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = l_string_join___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_5);
x_12 = l_list_repr__aux___main___rarg___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = l_list_repr__aux___main___rarg(x_0, x_1, x_7);
x_16 = lean::string_append(x_13, x_15);
lean::dec(x_15);
return x_16;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_19; 
lean::dec(x_0);
x_19 = l_string_join___closed__1;
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::dec(x_2);
lean::inc(x_0);
x_26 = lean::apply_1(x_0, x_20);
x_27 = 0;
x_28 = l_list_repr__aux___main___rarg(x_0, x_27, x_22);
x_29 = lean::string_append(x_26, x_28);
lean::dec(x_28);
return x_29;
}
}
}
}
obj* l_list_repr__aux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_list_repr__aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_list_repr__aux___main___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_list_repr__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_repr__aux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_repr__aux___rarg(obj* x_0, uint8 x_1, obj* x_2) {
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr__aux___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_list_repr__aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_list_repr__aux___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_list_repr__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_repr__aux(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_list_repr___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = l_list_repr___main___rarg___closed__1;
return x_3;
}
else
{
uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_4 = 1;
x_5 = l_list_repr__aux___main___rarg(x_0, x_4, x_1);
x_6 = l_list_repr___main___rarg___closed__2;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_9 = l_list_repr___main___rarg___closed__3;
x_10 = lean::string_append(x_7, x_9);
return x_10;
}
}
}
obj* l_list_repr___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___main___rarg), 2, 0);
return x_1;
}
}
obj* l_list_repr___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_repr___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___rarg), 2, 0);
return x_1;
}
}
obj* l_list_repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__repr___rarg), 1, 0);
return x_1;
}
}
obj* l_list_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_has__repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_unit_has__repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_unit_has__repr___closed__1;
return x_1;
}
}
obj* l_unit_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_unit_has__repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_option_has__repr___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = l_option_has__repr___rarg___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_option_has__repr___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_option_has__repr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
}
obj* l_option_has__repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option_has__repr___rarg), 2, 0);
return x_1;
}
}
obj* l_option_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option_has__repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_sum_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::apply_1(x_0, x_4);
x_8 = l_sum_has__repr___rarg___closed__1;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_option_has__repr___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::apply_1(x_1, x_14);
x_18 = l_sum_has__repr___rarg___closed__2;
x_19 = lean::string_append(x_18, x_17);
lean::dec(x_17);
x_21 = l_option_has__repr___rarg___closed__3;
x_22 = lean::string_append(x_19, x_21);
return x_22;
}
}
}
obj* l_sum_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_has__repr___rarg), 3, 0);
return x_2;
}
}
obj* l_sum_has__repr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_sum_has__repr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_prod_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::apply_1(x_0, x_3);
x_9 = l_prod_has__repr___rarg___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = l_list_repr__aux___main___rarg___closed__1;
x_13 = lean::string_append(x_10, x_12);
x_14 = lean::apply_1(x_1, x_5);
x_15 = lean::string_append(x_13, x_14);
lean::dec(x_14);
x_17 = l_option_has__repr___rarg___closed__3;
x_18 = lean::string_append(x_15, x_17);
return x_18;
}
}
obj* l_prod_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_has__repr___rarg), 3, 0);
return x_2;
}
}
obj* l_prod_has__repr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_prod_has__repr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_sigma_has__repr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_3);
x_9 = lean::apply_1(x_0, x_3);
x_10 = l_sigma_has__repr___rarg___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_13 = l_list_repr__aux___main___rarg___closed__1;
x_14 = lean::string_append(x_11, x_13);
x_15 = lean::apply_2(x_1, x_3, x_5);
x_16 = lean::string_append(x_14, x_15);
lean::dec(x_15);
x_18 = l_sigma_has__repr___rarg___closed__2;
x_19 = lean::string_append(x_16, x_18);
return x_19;
}
}
obj* l_sigma_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_has__repr___rarg), 3, 0);
return x_2;
}
}
obj* l_sigma_has__repr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_sigma_has__repr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_has__repr___rarg), 2, 0);
return x_2;
}
}
obj* l_subtype_has__repr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_subtype_has__repr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint32 l_nat_digit__char(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(2u);
x_6 = lean::nat_dec_eq(x_0, x_5);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(3u);
x_8 = lean::nat_dec_eq(x_0, x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(4u);
x_10 = lean::nat_dec_eq(x_0, x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(5u);
x_12 = lean::nat_dec_eq(x_0, x_11);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::mk_nat_obj(6u);
x_14 = lean::nat_dec_eq(x_0, x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = lean::mk_nat_obj(7u);
x_16 = lean::nat_dec_eq(x_0, x_15);
if (x_16 == 0)
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(8u);
x_18 = lean::nat_dec_eq(x_0, x_17);
if (x_18 == 0)
{
obj* x_19; uint8 x_20; 
x_19 = lean::mk_nat_obj(9u);
x_20 = lean::nat_dec_eq(x_0, x_19);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::mk_nat_obj(10u);
x_22 = lean::nat_dec_eq(x_0, x_21);
if (x_22 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::mk_nat_obj(11u);
x_24 = lean::nat_dec_eq(x_0, x_23);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
x_25 = lean::mk_nat_obj(12u);
x_26 = lean::nat_dec_eq(x_0, x_25);
if (x_26 == 0)
{
obj* x_27; uint8 x_28; 
x_27 = lean::mk_nat_obj(13u);
x_28 = lean::nat_dec_eq(x_0, x_27);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = lean::mk_nat_obj(14u);
x_30 = lean::nat_dec_eq(x_0, x_29);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(15u);
x_32 = lean::nat_dec_eq(x_0, x_31);
if (x_32 == 0)
{
uint32 x_33; 
x_33 = 42;
return x_33;
}
else
{
uint32 x_34; 
x_34 = 102;
return x_34;
}
}
else
{
uint32 x_35; 
x_35 = 101;
return x_35;
}
}
else
{
uint32 x_36; 
x_36 = 100;
return x_36;
}
}
else
{
uint32 x_37; 
x_37 = 99;
return x_37;
}
}
else
{
uint32 x_38; 
x_38 = 98;
return x_38;
}
}
else
{
uint32 x_39; 
x_39 = 97;
return x_39;
}
}
else
{
uint32 x_40; 
x_40 = 57;
return x_40;
}
}
else
{
uint32 x_41; 
x_41 = 56;
return x_41;
}
}
else
{
uint32 x_42; 
x_42 = 55;
return x_42;
}
}
else
{
uint32 x_43; 
x_43 = 54;
return x_43;
}
}
else
{
uint32 x_44; 
x_44 = 53;
return x_44;
}
}
else
{
uint32 x_45; 
x_45 = 52;
return x_45;
}
}
else
{
uint32 x_46; 
x_46 = 51;
return x_46;
}
}
else
{
uint32 x_47; 
x_47 = 50;
return x_47;
}
}
else
{
uint32 x_48; 
x_48 = 49;
return x_48;
}
}
else
{
uint32 x_49; 
x_49 = 48;
return x_49;
}
}
}
obj* l_nat_digit__char___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_nat_digit__char(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_nat_to__digits__core___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; uint32 x_7; obj* x_9; uint8 x_11; 
x_6 = lean::nat_mod(x_2, x_0);
x_7 = l_nat_digit__char(x_6);
lean::dec(x_6);
x_9 = lean::nat_div(x_2, x_0);
lean::dec(x_2);
x_11 = lean::nat_dec_eq(x_9, x_4);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_1, x_12);
lean::dec(x_1);
x_15 = lean::box_uint32(x_7);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_3);
x_1 = x_13;
x_2 = x_9;
x_3 = x_16;
goto _start;
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_1);
x_20 = lean::box_uint32(x_7);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_nat_to__digits__core___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_nat_to__digits__core___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_nat_to__digits__core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_nat_to__digits__core___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_nat_to__digits__core___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_nat_to__digits__core(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_nat_to__digits(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::nat_add(x_1, x_2);
x_4 = lean::box(0);
x_5 = l_nat_to__digits__core___main(x_0, x_3, x_1, x_4);
return x_5;
}
}
obj* l_nat_to__digits___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_nat_to__digits(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_nat_repr(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(10u);
x_2 = l_nat_to__digits(x_1, x_0);
x_3 = lean::string_mk(x_2);
return x_3;
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
uint32 x_1; obj* x_2; obj* x_3; 
x_1 = l_nat_digit__char(x_0);
x_2 = l_string_join___closed__1;
x_3 = lean::string_push(x_2, x_1);
return x_3;
}
}
obj* l_hex__digit__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_hex__digit__repr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_char__to__hex(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = lean::mk_nat_obj(16u);
x_3 = lean::nat_div(x_1, x_2);
x_4 = lean::nat_mod(x_1, x_2);
lean::dec(x_1);
x_6 = l_hex__digit__repr(x_3);
lean::dec(x_3);
x_8 = l_hex__digit__repr(x_4);
lean::dec(x_4);
x_10 = lean::string_append(x_6, x_8);
lean::dec(x_8);
return x_10;
}
}
obj* l_char__to__hex___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char__to__hex(x_1);
return x_2;
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
obj* l_char_quote__core(uint32 x_0) {
_start:
{
obj* x_1; uint32 x_3; uint8 x_4; 
x_3 = 10;
x_4 = x_0 == x_3;
if (x_4 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = 9;
x_6 = x_0 == x_5;
if (x_6 == 0)
{
obj* x_7; 
x_7 = lean::box(0);
x_1 = x_7;
goto lbl_2;
}
else
{
obj* x_8; 
x_8 = l_char_quote__core___closed__4;
return x_8;
}
}
else
{
obj* x_9; 
x_9 = l_char_quote__core___closed__5;
return x_9;
}
lbl_2:
{
uint32 x_11; uint8 x_12; 
lean::dec(x_1);
x_11 = 92;
x_12 = x_0 == x_11;
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 34;
x_14 = x_0 == x_13;
if (x_14 == 0)
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = lean::uint32_to_nat(x_0);
x_16 = lean::mk_nat_obj(31u);
x_17 = lean::nat_dec_le(x_15, x_16);
lean::dec(x_15);
if (x_17 == 0)
{
uint32 x_19; uint8 x_20; 
x_19 = 127;
x_20 = x_0 == x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = l_string_join___closed__1;
x_22 = lean::string_push(x_21, x_0);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = l_char__to__hex(x_0);
x_24 = l_char_quote__core___closed__1;
x_25 = lean::string_append(x_24, x_23);
lean::dec(x_23);
return x_25;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_char__to__hex(x_0);
x_28 = l_char_quote__core___closed__1;
x_29 = lean::string_append(x_28, x_27);
lean::dec(x_27);
return x_29;
}
}
else
{
obj* x_31; 
x_31 = l_char_quote__core___closed__2;
return x_31;
}
}
else
{
obj* x_32; 
x_32 = l_char_quote__core___closed__3;
return x_32;
}
}
}
}
obj* l_char_quote__core___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_quote__core(x_1);
return x_2;
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
obj* l_char_has__repr(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = l_char_quote__core(x_0);
x_2 = l_char_has__repr___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::string_append(x_3, x_2);
return x_5;
}
}
obj* l_char_has__repr___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
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
obj* x_1; 
x_1 = l_string_join___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_3; uint32 x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::unbox_uint32(x_2);
x_5 = l_char_quote__core(x_4);
x_6 = l_string_quote__aux___main(x_3);
x_7 = lean::string_append(x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
}
obj* l_string_quote__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_quote__aux___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_string_quote__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_quote__aux(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_string_quote(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_string_is__empty(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_2 = lean::string_data(x_0);
x_3 = l_string_quote__aux___main(x_2);
lean::dec(x_2);
x_5 = l_string_quote___closed__1;
x_6 = lean::string_append(x_5, x_3);
lean::dec(x_3);
x_8 = lean::string_append(x_6, x_5);
return x_8;
}
else
{
obj* x_10; 
lean::dec(x_0);
x_10 = l_string_quote___closed__2;
return x_10;
}
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
obj* _init_l_string_iterator_has__repr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(".mk_iterator");
return x_0;
}
}
obj* l_string_iterator_has__repr(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_remaining_to_string(x_0);
x_2 = l_string_quote(x_1);
x_3 = l_string_iterator_has__repr___closed__1;
x_4 = lean::string_append(x_2, x_3);
return x_4;
}
}
obj* l_string_iterator_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_iterator_has__repr(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_has__repr___rarg), 1, 0);
return x_1;
}
}
obj* l_fin_has__repr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_fin_has__repr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_uint16_has__repr(uint16 x_0) {
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
uint16 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_uint16_has__repr(x_1);
return x_2;
}
}
obj* l_uint32_has__repr(uint32 x_0) {
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
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_uint32_has__repr(x_1);
return x_2;
}
}
obj* l_uint64_has__repr(uint64 x_0) {
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
uint64 x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = l_uint64_has__repr(x_1);
return x_2;
}
}
obj* l_usize_has__repr(usize x_0) {
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
usize x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = l_usize_has__repr(x_1);
return x_2;
}
}
obj* l_char_repr(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = l_char_quote__core(x_0);
x_2 = l_char_has__repr___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::string_append(x_3, x_2);
return x_5;
}
}
obj* l_char_repr___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
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
lean::mark_persistent(l_bool_has__repr___closed__1);
 l_bool_has__repr___closed__2 = _init_l_bool_has__repr___closed__2();
lean::mark_persistent(l_bool_has__repr___closed__2);
 l_list_repr__aux___main___rarg___closed__1 = _init_l_list_repr__aux___main___rarg___closed__1();
lean::mark_persistent(l_list_repr__aux___main___rarg___closed__1);
 l_list_repr___main___rarg___closed__1 = _init_l_list_repr___main___rarg___closed__1();
lean::mark_persistent(l_list_repr___main___rarg___closed__1);
 l_list_repr___main___rarg___closed__2 = _init_l_list_repr___main___rarg___closed__2();
lean::mark_persistent(l_list_repr___main___rarg___closed__2);
 l_list_repr___main___rarg___closed__3 = _init_l_list_repr___main___rarg___closed__3();
lean::mark_persistent(l_list_repr___main___rarg___closed__3);
 l_unit_has__repr___closed__1 = _init_l_unit_has__repr___closed__1();
lean::mark_persistent(l_unit_has__repr___closed__1);
 l_option_has__repr___rarg___closed__1 = _init_l_option_has__repr___rarg___closed__1();
lean::mark_persistent(l_option_has__repr___rarg___closed__1);
 l_option_has__repr___rarg___closed__2 = _init_l_option_has__repr___rarg___closed__2();
lean::mark_persistent(l_option_has__repr___rarg___closed__2);
 l_option_has__repr___rarg___closed__3 = _init_l_option_has__repr___rarg___closed__3();
lean::mark_persistent(l_option_has__repr___rarg___closed__3);
 l_sum_has__repr___rarg___closed__1 = _init_l_sum_has__repr___rarg___closed__1();
lean::mark_persistent(l_sum_has__repr___rarg___closed__1);
 l_sum_has__repr___rarg___closed__2 = _init_l_sum_has__repr___rarg___closed__2();
lean::mark_persistent(l_sum_has__repr___rarg___closed__2);
 l_prod_has__repr___rarg___closed__1 = _init_l_prod_has__repr___rarg___closed__1();
lean::mark_persistent(l_prod_has__repr___rarg___closed__1);
 l_sigma_has__repr___rarg___closed__1 = _init_l_sigma_has__repr___rarg___closed__1();
lean::mark_persistent(l_sigma_has__repr___rarg___closed__1);
 l_sigma_has__repr___rarg___closed__2 = _init_l_sigma_has__repr___rarg___closed__2();
lean::mark_persistent(l_sigma_has__repr___rarg___closed__2);
 l_nat_has__repr = _init_l_nat_has__repr();
lean::mark_persistent(l_nat_has__repr);
 l_char_quote__core___closed__1 = _init_l_char_quote__core___closed__1();
lean::mark_persistent(l_char_quote__core___closed__1);
 l_char_quote__core___closed__2 = _init_l_char_quote__core___closed__2();
lean::mark_persistent(l_char_quote__core___closed__2);
 l_char_quote__core___closed__3 = _init_l_char_quote__core___closed__3();
lean::mark_persistent(l_char_quote__core___closed__3);
 l_char_quote__core___closed__4 = _init_l_char_quote__core___closed__4();
lean::mark_persistent(l_char_quote__core___closed__4);
 l_char_quote__core___closed__5 = _init_l_char_quote__core___closed__5();
lean::mark_persistent(l_char_quote__core___closed__5);
 l_char_has__repr___closed__1 = _init_l_char_has__repr___closed__1();
lean::mark_persistent(l_char_has__repr___closed__1);
 l_string_quote___closed__1 = _init_l_string_quote___closed__1();
lean::mark_persistent(l_string_quote___closed__1);
 l_string_quote___closed__2 = _init_l_string_quote___closed__2();
lean::mark_persistent(l_string_quote___closed__2);
 l_string_has__repr = _init_l_string_has__repr();
lean::mark_persistent(l_string_has__repr);
 l_string_iterator_has__repr___closed__1 = _init_l_string_iterator_has__repr___closed__1();
lean::mark_persistent(l_string_iterator_has__repr___closed__1);
}

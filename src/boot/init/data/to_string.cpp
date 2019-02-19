// Lean compiler output
// Module: init.data.to_string
// Imports: init.data.string.basic init.data.uint init.data.nat.div init.data.repr
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
obj* l_list_to__string__aux(obj*);
obj* l_list_to__string__aux___main___rarg(obj*, uint8, obj*);
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_usize_has__to__string___boxed(obj*);
obj* l_char_has__to__string(uint32);
extern obj* l_option_has__repr___rarg___closed__2;
obj* l_string_iterator_has__to__string(obj*);
obj* l_sigma_has__to__string(obj*, obj*);
extern obj* l_unit_has__repr___closed__1;
obj* l_uint32_has__to__string___boxed(obj*);
obj* l_uint16_has__to__string(uint16);
obj* l_list_to__string__aux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_list_to__string__aux___rarg(obj*, uint8, obj*);
obj* l_sum_has__to__string___rarg(obj*, obj*, obj*);
obj* l_prod_has__to__string(obj*, obj*);
obj* l_char_has__to__string___boxed(obj*);
obj* l_bool_has__to__string(uint8);
obj* l_unit_has__to__string(obj*);
obj* l_list_to__string(obj*);
obj* l_decidable_has__to__string(obj*);
extern obj* l_sum_has__repr___rarg___closed__1;
extern obj* l_option_has__repr___rarg___closed__1;
obj* l_prod_has__to__string___rarg(obj*, obj*, obj*);
obj* l_sum_has__to__string(obj*, obj*);
obj* l_id_has__to__string___rarg(obj*);
extern obj* l_list_repr___main___rarg___closed__1;
obj* l_option_has__to__string___rarg(obj*, obj*);
obj* l_fin_has__to__string(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_uint16_has__to__string___boxed(obj*);
obj* l_list_has__to__string(obj*);
obj* l_list_to__string___main(obj*);
obj* l_list_to__string__aux___rarg___boxed(obj*, obj*, obj*);
obj* l_list_to__string___main___rarg(obj*, obj*);
obj* l_option_has__to__string(obj*);
extern obj* l_sum_has__repr___rarg___closed__2;
obj* l_uint8_has__to__string___boxed(obj*);
extern obj* l_list_repr__aux___main___rarg___closed__1;
extern obj* l_list_repr___main___rarg___closed__3;
namespace lean {
obj* string_iterator_remaining_to_string(obj*);
}
obj* l_list_to__string___rarg(obj*, obj*);
obj* l_list_has__to__string___rarg(obj*);
obj* l_uint32_has__to__string(uint32);
obj* l_decidable_has__to__string___rarg(uint8);
extern obj* l_string_join___closed__1;
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_uint64_has__to__string(uint64);
extern obj* l_sigma_has__repr___rarg___closed__1;
obj* l_uint64_has__to__string___boxed(obj*);
obj* l_string_has__to__string(obj*);
obj* l_nat_has__to__string(obj*);
extern obj* l_list_repr___main___rarg___closed__2;
namespace lean {
obj* uint8_to_nat(uint8);
}
extern obj* l_bool_has__repr___closed__2;
obj* l_usize_has__to__string(usize);
extern obj* l_prod_has__repr___rarg___closed__1;
namespace lean {
obj* uint64_to_nat(uint64);
}
obj* l_id_has__to__string(obj*);
obj* l_bool_has__to__string___boxed(obj*);
obj* l_uint8_has__to__string(uint8);
extern obj* l_bool_has__repr___closed__1;
obj* l_fin_has__to__string___rarg(obj*);
obj* l_nat_repr(obj*);
extern obj* l_sigma_has__repr___rarg___closed__2;
obj* l_list_to__string__aux___main(obj*);
obj* l_sigma_has__to__string___rarg(obj*, obj*, obj*);
extern obj* l_option_has__repr___rarg___closed__3;
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_subtype_has__to__string___rarg(obj*, obj*);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_subtype_has__to__string(obj*, obj*);
obj* l_decidable_has__to__string___rarg___boxed(obj*);
obj* l_id_has__to__string___rarg(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_id_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id_has__to__string___rarg), 1, 0);
return x_2;
}
}
obj* l_string_has__to__string(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_string_iterator_has__to__string(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_bool_has__to__string(uint8 x_0) {
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
obj* l_bool_has__to__string___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_bool_has__to__string(x_1);
return x_2;
}
}
obj* l_decidable_has__to__string___rarg(uint8 x_0) {
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
obj* l_decidable_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_decidable_has__to__string___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_decidable_has__to__string___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_decidable_has__to__string___rarg(x_1);
return x_2;
}
}
obj* l_list_to__string__aux___main___rarg(obj* x_0, uint8 x_1, obj* x_2) {
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
x_15 = l_list_to__string__aux___main___rarg(x_0, x_1, x_7);
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
x_28 = l_list_to__string__aux___main___rarg(x_0, x_27, x_22);
x_29 = lean::string_append(x_26, x_28);
lean::dec(x_28);
return x_29;
}
}
}
}
obj* l_list_to__string__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__string__aux___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_to__string__aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_list_to__string__aux___main___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_list_to__string__aux___rarg(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_to__string__aux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_to__string__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__string__aux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_list_to__string__aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_list_to__string__aux___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_list_to__string___main___rarg(obj* x_0, obj* x_1) {
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
x_5 = l_list_to__string__aux___main___rarg(x_0, x_4, x_1);
x_6 = l_list_repr___main___rarg___closed__2;
x_7 = lean::string_append(x_6, x_5);
lean::dec(x_5);
x_9 = l_list_repr___main___rarg___closed__3;
x_10 = lean::string_append(x_7, x_9);
return x_10;
}
}
}
obj* l_list_to__string___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__string___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_to__string___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_to__string___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__string___rarg), 2, 0);
return x_2;
}
}
obj* l_list_has__to__string___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__string___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_has__to__string___rarg), 1, 0);
return x_2;
}
}
obj* l_unit_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_unit_has__repr___closed__1;
return x_2;
}
}
obj* l_nat_has__to__string(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_nat_repr(x_0);
return x_1;
}
}
obj* l_char_has__to__string(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_string_join___closed__1;
x_2 = lean::string_push(x_1, x_0);
return x_2;
}
}
obj* l_char_has__to__string___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_has__to__string(x_1);
return x_2;
}
}
obj* l_fin_has__to__string___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_nat_repr(x_0);
return x_1;
}
}
obj* l_fin_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fin_has__to__string___rarg), 1, 0);
return x_2;
}
}
obj* l_uint8_has__to__string(uint8 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint8_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint8_has__to__string___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_uint8_has__to__string(x_1);
return x_2;
}
}
obj* l_uint16_has__to__string(uint16 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint16_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint16_has__to__string___boxed(obj* x_0) {
_start:
{
uint16 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_uint16_has__to__string(x_1);
return x_2;
}
}
obj* l_uint32_has__to__string(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint32_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint32_has__to__string___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_uint32_has__to__string(x_1);
return x_2;
}
}
obj* l_uint64_has__to__string(uint64 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::uint64_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_uint64_has__to__string___boxed(obj* x_0) {
_start:
{
uint64 x_1; obj* x_2; 
x_1 = lean::unbox_uint64(x_0);
x_2 = l_uint64_has__to__string(x_1);
return x_2;
}
}
obj* l_usize_has__to__string(usize x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::usize_to_nat(x_0);
x_2 = l_nat_repr(x_1);
return x_2;
}
}
obj* l_usize_has__to__string___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::unbox_size_t(x_0);
x_2 = l_usize_has__to__string(x_1);
return x_2;
}
}
obj* l_option_has__to__string___rarg(obj* x_0, obj* x_1) {
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
obj* l_option_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_has__to__string___rarg), 2, 0);
return x_2;
}
}
obj* l_sum_has__to__string___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_sum_has__to__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sum_has__to__string___rarg), 3, 0);
return x_4;
}
}
obj* l_prod_has__to__string___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_prod_has__to__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_prod_has__to__string___rarg), 3, 0);
return x_4;
}
}
obj* l_sigma_has__to__string___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_sigma_has__to__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_sigma_has__to__string___rarg), 3, 0);
return x_4;
}
}
obj* l_subtype_has__to__string___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_subtype_has__to__string(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_subtype_has__to__string___rarg), 2, 0);
return x_4;
}
}
void initialize_init_data_string_basic();
void initialize_init_data_uint();
void initialize_init_data_nat_div();
void initialize_init_data_repr();
static bool _G_initialized = false;
void initialize_init_data_to__string() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_string_basic();
 initialize_init_data_uint();
 initialize_init_data_nat_div();
 initialize_init_data_repr();
}

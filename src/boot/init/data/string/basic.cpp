// Lean compiler output
// Module: init.data.string.basic
// Imports: init.data.list.basic init.data.char.basic init.data.option.basic
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
obj* l_string_iterator_next___boxed(obj*);
obj* l_string_backn(obj*, obj*);
obj* l_string_iterator_prevn(obj*, obj*);
namespace lean {
obj* string_iterator_prev_to_string(obj*);
}
uint32 l_string_front(obj*);
uint8 l_char_is__whitespace(uint32);
obj* l___private_init_data_string_basic_2__trim__right__aux(obj*, obj*);
obj* l_string_iterator_prev__to__string___boxed(obj*);
obj* l___private_init_data_string_basic_1__trim__left__aux___main(obj*, obj*);
obj* l_string_pushn___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_string_has__lt;
obj* l_string_iterator_remaining___boxed(obj*);
obj* l_string_iterator_forward(obj*, obj*);
obj* l_string_decidable__eq;
obj* l_string_line__column___closed__1;
obj* l_string_singleton(uint32);
obj* l_string_pushn(obj*, uint32, obj*);
obj* l_list_as__string(obj*);
obj* l_string_iterator_is__prefix__of__remaining;
obj* l_string_iterator_forward___main(obj*, obj*);
obj* l_string_iterator_has__next___boxed(obj*);
obj* l_nat_repeat__core___main___at_string_pushn___spec__1(uint32, obj*, obj*, obj*);
obj* l_string_iterator_extract__core(obj*, obj*);
obj* l_string_back___boxed(obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_string_singleton___boxed(obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_string_front___boxed(obj*);
uint8 l_string_is__empty(obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
namespace lean {
obj* string_iterator_set_curr(obj*, uint32);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_string_iterator_insert___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__to__nat__core(obj*, obj*, obj*);
obj* l_string_pop__back(obj*);
obj* l_string_intercalate(obj*, obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
obj* l_char_to__string___boxed(obj*);
namespace lean {
obj* string_iterator_to_end(obj*);
}
obj* l_string_iterator_curr___boxed(obj*);
namespace lean {
obj* string_iterator_extract(obj*, obj*);
}
uint32 l_string_back(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
namespace lean {
obj* string_data(obj*);
}
obj* l_string_append___boxed(obj*, obj*);
obj* l_string_str(obj*, uint32);
obj* l_string_to__nat(obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
obj* string_iterator_remaining_to_string(obj*);
}
obj* l_string_line__column(obj*, obj*);
obj* l_string_iterator_nextn___main(obj*, obj*);
obj* l_string_length___boxed(obj*);
obj* l___private_init_data_string_basic_2__trim__right__aux___main(obj*, obj*);
obj* l_string_iterator_to__string___boxed(obj*);
obj* l_string_iterator_remove___boxed(obj*, obj*);
obj* l_string_join___closed__1;
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l___private_init_data_string_basic_1__trim__left__aux(obj*, obj*);
obj* l_string_iterator_offset___boxed(obj*);
obj* l___private_init_data_string_basic_3__line__column__aux(obj*, obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l___private_init_data_string_basic_3__line__column__aux___main(obj*, obj*, obj*);
obj* l_string_has__append;
namespace lean {
obj* string_iterator_prev(obj*);
}
obj* l_string_iterator_prevn___main(obj*, obj*);
namespace lean {
obj* string_iterator_remove(obj*, obj*);
}
obj* l_string_popn__back(obj*, obj*);
obj* l_list_intercalate___rarg(obj*, obj*);
namespace lean {
obj* string_iterator_offset(obj*);
}
namespace lean {
obj* string_mk(obj*);
}
obj* l_string_inhabited;
obj* l_string_join(obj*);
uint8 l_string_iterator_decidable__rel(obj*, obj*);
obj* l_string_push___boxed(obj*, obj*);
obj* l_string_dec__eq___boxed(obj*, obj*);
obj* l_string_mk__iterator___boxed(obj*);
obj* l_string_iterator_decidable__rel___boxed(obj*, obj*);
obj* l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1___boxed(obj*, obj*);
obj* l_string_iterator_nextn(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_string_trim__right(obj*);
obj* l_string_iterator_extract__core___main(obj*, obj*);
namespace lean {
obj* string_iterator_insert(obj*, obj*);
}
obj* l_char_to__string(uint32);
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_list_map___main___at_string_intercalate___spec__1(obj*);
obj* l_string_has__sizeof;
obj* l_string_to__list(obj*);
obj* l_string_trim(obj*);
uint8 l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(obj*, obj*);
obj* l_string_iterator_set__curr___boxed(obj*, obj*);
obj* l_nat_repeat__core___main___at_string_pushn___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_string_iterator_prev___boxed(obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l___private_init_data_string_basic_4__to__nat__core___main(obj*, obj*, obj*);
obj* l_string_is__empty___boxed(obj*);
namespace lean {
uint8 string_iterator_has_prev(obj*);
}
obj* l_string_iterator_to__end___boxed(obj*);
obj* l_string_iterator_extract___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_string_trim__left(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_string_str___boxed(obj*, obj*);
obj* l_string_iterator_remaining__to__string___boxed(obj*);
namespace lean {
obj* string_iterator_to_string(obj*);
}
obj* l_string_iterator_has__prev___boxed(obj*);
obj* l_string_dec__lt___boxed(obj*, obj*);
obj* l_string_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::string_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_string_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l_list_as__string(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_mk(x_0);
return x_1;
}
}
obj* _init_l_string_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_string_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::string_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_string_length___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_length(x_0);
return x_1;
}
}
obj* l_string_push___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = lean::string_push(x_0, x_2);
return x_3;
}
}
obj* l_string_append___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_append(x_0, x_1);
return x_2;
}
}
obj* l_string_to__list(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_data(x_0);
return x_1;
}
}
obj* l_string_mk__iterator___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_mk_iterator(x_0);
return x_1;
}
}
obj* l_string_iterator_remaining___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_remaining(x_0);
return x_1;
}
}
obj* l_string_iterator_offset___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_offset(x_0);
return x_1;
}
}
obj* l_string_iterator_curr___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::string_iterator_curr(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
obj* l_string_iterator_set__curr___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = lean::string_iterator_set_curr(x_0, x_2);
return x_3;
}
}
obj* l_string_iterator_next___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_next(x_0);
return x_1;
}
}
obj* l_string_iterator_prev___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_prev(x_0);
return x_1;
}
}
obj* l_string_iterator_has__next___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::string_iterator_has_next(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_string_iterator_has__prev___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::string_iterator_has_prev(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_string_iterator_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_iterator_insert(x_0, x_1);
return x_2;
}
}
obj* l_string_iterator_remove___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_iterator_remove(x_0, x_1);
return x_2;
}
}
obj* l_string_iterator_to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_to_string(x_0);
return x_1;
}
}
obj* l_string_iterator_forward___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = lean::string_iterator_next(x_0);
x_0 = x_7;
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_string_iterator_forward(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_string_iterator_forward___main(x_0, x_1);
return x_2;
}
}
obj* l_string_iterator_to__end___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_to_end(x_0);
return x_1;
}
}
obj* l_string_iterator_remaining__to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_remaining_to_string(x_0);
return x_1;
}
}
obj* l_string_iterator_prev__to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_prev_to_string(x_0);
return x_1;
}
}
uint8 l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_4; 
lean::dec(x_1);
x_4 = 0;
return x_4;
}
}
else
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_12; 
lean::dec(x_5);
lean::dec(x_7);
x_12 = 0;
return x_12;
}
else
{
obj* x_13; obj* x_15; uint32 x_18; uint32 x_19; uint8 x_20; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::dec(x_1);
x_18 = lean::unbox_uint32(x_5);
x_19 = lean::unbox_uint32(x_13);
x_20 = x_18 == x_19;
if (x_20 == 0)
{
uint8 x_23; 
lean::dec(x_15);
lean::dec(x_7);
x_23 = 0;
return x_23;
}
else
{
uint8 x_24; 
x_24 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_7, x_15);
if (x_24 == 0)
{
uint8 x_25; 
x_25 = 0;
return x_25;
}
else
{
uint8 x_26; 
x_26 = 1;
return x_26;
}
}
}
}
}
}
obj* l_string_iterator_extract__core___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; uint8 x_11; 
x_4 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_8 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_6);
x_11 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_6, x_1);
if (x_11 == 0)
{
obj* x_12; 
x_12 = l_string_iterator_extract__core___main(x_6, x_1);
if (lean::obj_tag(x_12) == 0)
{
lean::dec(x_8);
lean::dec(x_4);
return x_12;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_17 = x_12;
} else {
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_8;
}
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_15);
if (lean::is_scalar(x_17)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_17;
}
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_6);
lean::dec(x_1);
x_22 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
}
}
obj* l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_string_iterator_extract__core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_string_iterator_extract__core___main(x_0, x_1);
return x_2;
}
}
obj* l_string_iterator_extract___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_iterator_extract(x_0, x_1);
return x_2;
}
}
obj* _init_l_string_iterator_is__prefix__of__remaining() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_string_iterator_decidable__rel(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
lean::inc(x_1);
x_4 = l_string_iterator_forward___main(x_1, x_2);
x_5 = lean::string_iterator_extract(x_1, x_4);
lean::dec(x_4);
lean::dec(x_1);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_9; 
lean::dec(x_0);
x_9 = 0;
return x_9;
}
else
{
obj* x_10; obj* x_13; uint8 x_15; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
x_15 = lean::string_dec_eq(x_10, x_13);
lean::dec(x_13);
lean::dec(x_10);
if (x_15 == 0)
{
uint8 x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
}
}
}
obj* l_string_iterator_decidable__rel___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_string_iterator_decidable__rel(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_string_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
obj* _init_l_string_has__sizeof() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_length___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_string_has__append() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_append___boxed), 2, 0);
return x_0;
}
}
obj* l_string_str(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_push(x_0, x_1);
return x_2;
}
}
obj* l_string_str___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_string_str(x_0, x_2);
return x_3;
}
}
obj* l_nat_repeat__core___main___at_string_pushn___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_9 = lean::string_push(x_3, x_0);
x_2 = x_7;
x_3 = x_9;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_string_pushn(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::inc(x_2);
x_4 = l_nat_repeat__core___main___at_string_pushn___spec__1(x_1, x_2, x_2, x_0);
return x_4;
}
}
obj* l_nat_repeat__core___main___at_string_pushn___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_nat_repeat__core___main___at_string_pushn___spec__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_string_pushn___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_string_pushn(x_0, x_3, x_2);
return x_4;
}
}
uint8 l_string_is__empty(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; uint8 x_4; 
x_1 = lean::string_length(x_0);
lean::dec(x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
lean::dec(x_1);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
obj* l_string_is__empty___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_string_is__empty(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint32 l_string_front(obj* x_0) {
_start:
{
obj* x_1; uint32 x_2; 
x_1 = lean::string_mk_iterator(x_0);
x_2 = lean::string_iterator_curr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_string_front___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_string_front(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
uint32 l_string_back(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint32 x_4; 
x_1 = lean::string_mk_iterator(x_0);
x_2 = lean::string_iterator_to_end(x_1);
x_3 = lean::string_iterator_prev(x_2);
x_4 = lean::string_iterator_curr(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_string_back___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = l_string_back(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
obj* l_list_foldl___main___at_string_join___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::string_append(x_0, x_2);
lean::dec(x_2);
x_0 = x_7;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_string_join___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
obj* l_string_join(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_string_join___closed__1;
x_2 = l_list_foldl___main___at_string_join___spec__1(x_1, x_0);
return x_2;
}
}
obj* l_string_singleton(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_string_join___closed__1;
x_2 = lean::string_push(x_1, x_0);
return x_2;
}
}
obj* l_string_singleton___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_string_singleton(x_1);
return x_2;
}
}
obj* l_list_map___main___at_string_intercalate___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::string_data(x_2);
x_8 = l_list_map___main___at_string_intercalate___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_string_intercalate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_data(x_0);
x_3 = l_list_map___main___at_string_intercalate___spec__1(x_1);
x_4 = l_list_intercalate___rarg(x_2, x_3);
x_5 = lean::string_mk(x_4);
return x_5;
}
}
obj* l_string_iterator_nextn___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = lean::string_iterator_next(x_0);
x_0 = x_7;
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_string_iterator_nextn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_string_iterator_nextn___main(x_0, x_1);
return x_2;
}
}
obj* l_string_iterator_prevn___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_7; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_1, x_4);
lean::dec(x_1);
x_7 = lean::string_iterator_prev(x_0);
x_0 = x_7;
x_1 = x_5;
goto _start;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
obj* l_string_iterator_prevn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_string_iterator_prevn___main(x_0, x_1);
return x_2;
}
}
obj* l_string_pop__back(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_mk_iterator(x_0);
x_2 = lean::string_iterator_to_end(x_1);
x_3 = lean::string_iterator_prev(x_2);
x_4 = lean::string_iterator_prev_to_string(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_string_popn__back(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::string_iterator_to_end(x_2);
x_4 = l_string_iterator_prevn___main(x_3, x_1);
x_5 = lean::string_iterator_prev_to_string(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_string_backn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::string_iterator_to_end(x_2);
x_4 = l_string_iterator_prevn___main(x_3, x_1);
x_5 = lean::string_iterator_remaining_to_string(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_1__trim__left__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = lean::string_iterator_curr(x_1);
x_5 = l_char_is__whitespace(x_4);
if (x_5 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_0, x_7);
lean::dec(x_0);
x_10 = lean::string_iterator_next(x_1);
x_0 = x_8;
x_1 = x_10;
goto _start;
}
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l___private_init_data_string_basic_1__trim__left__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_string_basic_1__trim__left__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_string_trim__left(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = l___private_init_data_string_basic_1__trim__left__aux___main(x_1, x_2);
x_4 = lean::string_iterator_remaining_to_string(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_2__trim__right__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
if (x_3 == 0)
{
obj* x_5; uint32 x_6; uint8 x_7; 
lean::inc(x_1);
x_5 = lean::string_iterator_prev(x_1);
x_6 = lean::string_iterator_curr(x_5);
x_7 = l_char_is__whitespace(x_6);
if (x_7 == 0)
{
lean::dec(x_5);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_1);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_0 = x_12;
x_1 = x_5;
goto _start;
}
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* l___private_init_data_string_basic_2__trim__right__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_string_basic_2__trim__right__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_string_trim__right(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::string_iterator_to_end(x_2);
x_4 = l___private_init_data_string_basic_2__trim__right__aux___main(x_1, x_3);
x_5 = lean::string_iterator_prev_to_string(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_string_trim(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
lean::inc(x_2);
lean::inc(x_1);
x_5 = l___private_init_data_string_basic_1__trim__left__aux___main(x_1, x_2);
x_6 = lean::string_iterator_to_end(x_2);
x_7 = l___private_init_data_string_basic_2__trim__right__aux___main(x_1, x_6);
x_8 = lean::string_iterator_extract(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
x_11 = l_string_join___closed__1;
x_12 = l_option_get__or__else___main___rarg(x_8, x_11);
return x_12;
}
}
obj* l___private_init_data_string_basic_3__line__column__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_7; uint8 x_9; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::string_iterator_has_next(x_1);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_15; obj* x_16; uint32 x_18; uint32 x_19; uint8 x_20; 
lean::dec(x_2);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_0, x_15);
lean::dec(x_0);
x_18 = lean::string_iterator_curr(x_1);
x_19 = 10;
x_20 = x_18 == x_19;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_24; 
x_21 = lean::string_iterator_next(x_1);
x_22 = lean::nat_add(x_7, x_15);
lean::dec(x_7);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_22);
x_0 = x_16;
x_1 = x_21;
x_2 = x_24;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_7);
x_27 = lean::string_iterator_next(x_1);
x_28 = lean::nat_add(x_5, x_15);
lean::dec(x_5);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_3);
x_0 = x_16;
x_1 = x_27;
x_2 = x_30;
goto _start;
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_data_string_basic_3__line__column__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_3__line__column__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_string_line__column___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_string_line__column(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_string_line__column___closed__1;
x_4 = l___private_init_data_string_basic_3__line__column__aux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_char_to__string(uint32 x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_string_join___closed__1;
x_2 = lean::string_push(x_1, x_0);
return x_2;
}
}
obj* l_char_to__string___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__string(x_1);
return x_2;
}
}
obj* _init_l___private_init_data_string_basic_4__to__nat__core___main___closed__1() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = 48;
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l___private_init_data_string_basic_4__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint32 x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
x_8 = lean::string_iterator_curr(x_0);
x_9 = lean::mk_nat_obj(10u);
x_10 = lean::nat_mul(x_2, x_9);
lean::dec(x_2);
x_12 = lean::uint32_to_nat(x_8);
x_13 = lean::nat_add(x_10, x_12);
lean::dec(x_12);
lean::dec(x_10);
x_16 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_17 = lean::nat_sub(x_13, x_16);
lean::dec(x_13);
x_19 = lean::string_iterator_next(x_0);
x_0 = x_19;
x_1 = x_6;
x_2 = x_17;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_data_string_basic_4__to__nat__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_4__to__nat__core___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_string_to__nat(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::string_length(x_0);
lean::dec(x_0);
x_5 = lean::mk_nat_obj(0u);
x_6 = l___private_init_data_string_basic_4__to__nat__core___main(x_2, x_3, x_5);
return x_6;
}
}
void initialize_init_data_list_basic();
void initialize_init_data_char_basic();
void initialize_init_data_option_basic();
static bool _G_initialized = false;
void initialize_init_data_string_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_list_basic();
 initialize_init_data_char_basic();
 initialize_init_data_option_basic();
 l_string_decidable__eq = _init_l_string_decidable__eq();
lean::mark_persistent(l_string_decidable__eq);
 l_string_has__lt = _init_l_string_has__lt();
lean::mark_persistent(l_string_has__lt);
 l_string_iterator_is__prefix__of__remaining = _init_l_string_iterator_is__prefix__of__remaining();
lean::mark_persistent(l_string_iterator_is__prefix__of__remaining);
 l_string_inhabited = _init_l_string_inhabited();
lean::mark_persistent(l_string_inhabited);
 l_string_has__sizeof = _init_l_string_has__sizeof();
lean::mark_persistent(l_string_has__sizeof);
 l_string_has__append = _init_l_string_has__append();
lean::mark_persistent(l_string_has__append);
 l_string_join___closed__1 = _init_l_string_join___closed__1();
lean::mark_persistent(l_string_join___closed__1);
 l_string_line__column___closed__1 = _init_l_string_line__column___closed__1();
lean::mark_persistent(l_string_line__column___closed__1);
 l___private_init_data_string_basic_4__to__nat__core___main___closed__1 = _init_l___private_init_data_string_basic_4__to__nat__core___main___closed__1();
lean::mark_persistent(l___private_init_data_string_basic_4__to__nat__core___main___closed__1);
}

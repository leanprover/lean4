// Lean compiler output
// Module: init.data.string.basic
// Imports: init.data.list.basic init.data.char.basic init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_string_iterator_to__end___main(obj*);
obj* l_string_iterator_next___boxed(obj*);
obj* l_string_iterator_has__prev___main___boxed(obj*);
obj* l_string_backn(obj*, obj*);
obj* l_string_iterator_prevn(obj*, obj*);
uint32 l_string_front(obj*);
uint8 l_char_is__whitespace(uint32);
obj* l___private_init_data_string_basic_2__trim__right__aux(obj*, obj*);
obj* l_string_iterator_prev__to__string___boxed(obj*);
obj* l___private_init_data_string_basic_1__trim__left__aux___main(obj*, obj*);
obj* l_string_pushn___boxed(obj*, obj*, obj*);
obj* l_string_has__lt;
obj* l_string_iterator_remaining___boxed(obj*);
obj* l_string_iterator_forward(obj*, obj*);
obj* l_string_iterator_extract___main___closed__1;
obj* l_string_decidable__eq;
obj* l_string_line__column___closed__1;
obj* l_string_singleton(uint32);
obj* l_string_pushn(obj*, uint32, obj*);
obj* l_list_as__string(obj*);
obj* l_string_iterator_is__prefix__of__remaining;
obj* l_string_iterator_forward___main(obj*, obj*);
obj* l_string_iterator_offset___main(obj*);
obj* l_string_iterator_extract___main(obj*, obj*);
obj* l_string_iterator_has__next___boxed(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_string_push___main___boxed(obj*, obj*);
uint8 l_string_iterator_has__prev___main(obj*);
obj* l_nat_repeat__core___main___at_string_pushn___spec__1(uint32, obj*, obj*, obj*);
obj* l_string_iterator_extract__core(obj*, obj*);
obj* l_string_back___boxed(obj*);
obj* l_string_singleton___boxed(obj*);
obj* l_string_iterator_remaining__to__string___main(obj*);
obj* l_string_front___boxed(obj*);
uint8 l_string_is__empty(obj*);
obj* l_string_mk__iterator___main(obj*);
obj* l_string_iterator_insert___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_4__to__nat__core(obj*, obj*, obj*);
obj* l_string_pop__back(obj*);
obj* l_string_intercalate(obj*, obj*);
obj* l_char_to__string___boxed(obj*);
obj* l_string_iterator_remaining___main(obj*);
obj* l_string_iterator_curr___boxed(obj*);
uint32 l_string_back(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_string_iterator_prev___main(obj*);
obj* l_string_iterator_to__string___main(obj*);
obj* l_string_append___boxed(obj*, obj*);
obj* l_string_str(obj*, uint32);
obj* l_string_to__nat(obj*);
obj* l_list_drop___main___rarg(obj*, obj*);
obj* l_string_line__column(obj*, obj*);
obj* l_string_iterator_set__curr___main(obj*, uint32);
obj* l_string_iterator_nextn___main(obj*, obj*);
obj* l_string_length___boxed(obj*);
obj* l___private_init_data_string_basic_2__trim__right__aux___main(obj*, obj*);
obj* l_string_iterator_has__next___main___boxed(obj*);
obj* l_string_iterator_to__string___boxed(obj*);
obj* l_string_iterator_remove___boxed(obj*, obj*);
obj* l_string_join___closed__1;
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l___private_init_data_string_basic_1__trim__left__aux(obj*, obj*);
obj* l_string_iterator_offset___boxed(obj*);
extern obj* l_char_inhabited;
obj* l___private_init_data_string_basic_3__line__column__aux(obj*, obj*, obj*);
obj* l_string_iterator_insert___main(obj*, obj*);
obj* l___private_init_data_string_basic_3__line__column__aux___main(obj*, obj*, obj*);
obj* l_string_has__append;
obj* l_string_iterator_prevn___main(obj*, obj*);
obj* l_string_popn__back(obj*, obj*);
obj* l_list_intercalate___rarg(obj*, obj*);
obj* l_string_inhabited;
obj* l_string_join(obj*);
uint8 l_string_iterator_decidable__rel(obj*, obj*);
obj* l_string_push___boxed(obj*, obj*);
obj* l_string_dec__eq___boxed(obj*, obj*);
obj* l_string_mk__iterator___boxed(obj*);
obj* l_string_iterator_decidable__rel___boxed(obj*, obj*);
obj* l_string_append___main(obj*, obj*);
obj* l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1___boxed(obj*, obj*);
obj* l_string_iterator_nextn(obj*, obj*);
obj* l_string_trim__right(obj*);
obj* l_string_iterator_extract__core___main(obj*, obj*);
obj* l_string_push___main(obj*, uint32);
obj* l_char_to__string(uint32);
obj* l_list_map___main___at_string_intercalate___spec__1(obj*);
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_string_has__sizeof;
obj* l_string_to__list(obj*);
obj* l_string_trim(obj*);
uint8 l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(obj*, obj*);
obj* l_string_iterator_curr___main(obj*);
obj* l_string_iterator_set__curr___boxed(obj*, obj*);
obj* l_nat_repeat__core___main___at_string_pushn___spec__1___boxed(obj*, obj*, obj*, obj*);
uint8 l_string_iterator_has__next___main(obj*);
obj* l_string_iterator_prev___boxed(obj*);
obj* l_string_iterator_prev__to__string___main(obj*);
obj* l___private_init_data_string_basic_4__to__nat__core___main(obj*, obj*, obj*);
obj* l_string_is__empty___boxed(obj*);
obj* l_string_iterator_to__end___boxed(obj*);
obj* l_string_iterator_extract___boxed(obj*, obj*);
obj* l_string_iterator_set__curr___main___boxed(obj*, obj*);
obj* l_string_trim__left(obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_string_str___boxed(obj*, obj*);
obj* l_string_iterator_remaining__to__string___boxed(obj*);
obj* l_string_iterator_remove___main(obj*, obj*);
obj* l_string_iterator_next___main(obj*);
obj* l_string_iterator_has__prev___boxed(obj*);
obj* l_string_dec__lt___boxed(obj*, obj*);
obj* l_string_length___main(obj*);
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
obj* l_string_length___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_data(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = l_list_length__aux___main___rarg(x_1, x_2);
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
obj* l_string_push___main(obj* x_0, uint32 x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_data(x_0);
x_3 = lean::box(0);
x_4 = lean::box_uint32(x_1);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = l_list_append___rarg(x_2, x_5);
x_7 = lean::string_mk(x_6);
return x_7;
}
}
obj* l_string_push___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_string_push___main(x_0, x_2);
return x_3;
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
obj* l_string_append___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_data(x_0);
x_3 = lean::string_data(x_1);
x_4 = l_list_append___rarg(x_2, x_3);
x_5 = lean::string_mk(x_4);
return x_5;
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
obj* l_string_mk__iterator___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_data(x_0);
x_2 = lean::box(0);
x_3 = lean::string_iterator_mk(x_2, x_1);
return x_3;
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
obj* l_string_iterator_remaining___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_iterator_snd(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = l_list_length__aux___main___rarg(x_1, x_2);
return x_3;
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
obj* l_string_iterator_offset___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_iterator_fst(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = l_list_length__aux___main___rarg(x_1, x_2);
return x_3;
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
obj* l_string_iterator_curr___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_snd(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_char_inhabited;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
return x_5;
}
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
obj* l_string_iterator_set__curr___main(obj* x_0, uint32 x_1) {
_start:
{
obj* x_3; 
lean::inc(x_0);
x_3 = lean::string_iterator_snd(x_0);
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_3);
return x_0;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_7 = x_3;
}
x_8 = lean::string_iterator_fst(x_0);
x_9 = lean::box_uint32(x_1);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
x_11 = lean::string_iterator_mk(x_8, x_10);
return x_11;
}
}
}
obj* l_string_iterator_set__curr___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_string_iterator_set__curr___main(x_0, x_2);
return x_3;
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
obj* l_string_iterator_next___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::string_iterator_snd(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_0;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_8 = x_2;
}
x_9 = lean::string_iterator_fst(x_0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::string_iterator_mk(x_10, x_6);
return x_11;
}
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
obj* l_string_iterator_prev___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = lean::string_iterator_fst(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_0;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_8 = x_2;
}
x_9 = lean::string_iterator_snd(x_0);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::string_iterator_mk(x_6, x_10);
return x_11;
}
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
uint8 l_string_iterator_has__next___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_snd(x_0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 0;
return x_3;
}
else
{
uint8 x_5; 
lean::dec(x_1);
x_5 = 1;
return x_5;
}
}
}
obj* l_string_iterator_has__next___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_string_iterator_has__next___main(x_0);
x_2 = lean::box(x_1);
return x_2;
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
uint8 l_string_iterator_has__prev___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_fst(x_0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 0;
return x_3;
}
else
{
uint8 x_5; 
lean::dec(x_1);
x_5 = 1;
return x_5;
}
}
}
obj* l_string_iterator_has__prev___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_string_iterator_has__prev___main(x_0);
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
obj* l_string_iterator_insert___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_0);
x_3 = lean::string_iterator_fst(x_0);
x_4 = lean::string_iterator_snd(x_0);
x_5 = lean::string_data(x_1);
x_6 = l_list_append___rarg(x_5, x_4);
x_7 = lean::string_iterator_mk(x_3, x_6);
return x_7;
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
obj* l_string_iterator_remove___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_3 = lean::string_iterator_fst(x_0);
x_4 = lean::string_iterator_snd(x_0);
x_5 = l_list_drop___main___rarg(x_1, x_4);
x_6 = lean::string_iterator_mk(x_3, x_5);
return x_6;
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
obj* l_string_iterator_to__string___main(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_2 = lean::string_iterator_fst(x_0);
x_3 = lean::string_iterator_snd(x_0);
x_4 = l_list_reverse___rarg(x_2);
x_5 = l_list_append___rarg(x_4, x_3);
x_6 = lean::string_mk(x_5);
return x_6;
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
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::string_iterator_next(x_0);
x_0 = x_9;
x_1 = x_6;
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
obj* l_string_iterator_to__end___main(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_0);
x_2 = lean::string_iterator_fst(x_0);
x_3 = lean::string_iterator_snd(x_0);
x_4 = l_list_reverse___rarg(x_3);
x_5 = l_list_append___rarg(x_4, x_2);
x_6 = lean::box(0);
x_7 = lean::string_iterator_mk(x_5, x_6);
return x_7;
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
obj* l_string_iterator_remaining__to__string___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::string_iterator_snd(x_0);
x_2 = lean::string_mk(x_1);
return x_2;
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
obj* l_string_iterator_prev__to__string___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::string_iterator_fst(x_0);
x_2 = l_list_reverse___rarg(x_1);
x_3 = lean::string_mk(x_2);
return x_3;
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
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
lean::dec(x_1);
x_4 = 1;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_1);
x_6 = 0;
return x_6;
}
}
else
{
obj* x_7; obj* x_9; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
uint8 x_15; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
x_15 = 0;
return x_15;
}
else
{
obj* x_16; obj* x_18; uint8 x_21; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::nat_dec_eq(x_7, x_16);
lean::dec(x_16);
lean::dec(x_7);
if (x_21 == 0)
{
uint8 x_26; 
lean::dec(x_9);
lean::dec(x_18);
x_26 = 0;
return x_26;
}
else
{
uint8 x_27; 
x_27 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_9, x_18);
if (x_27 == 0)
{
uint8 x_28; 
x_28 = 0;
return x_28;
}
else
{
uint8 x_29; 
x_29 = 1;
return x_29;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
lean::inc(x_1);
lean::inc(x_7);
x_12 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_7, x_1);
if (x_12 == 0)
{
obj* x_13; 
x_13 = l_string_iterator_extract__core___main(x_7, x_1);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_9);
lean::dec(x_5);
return x_13;
}
else
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_18 = x_13;
}
if (lean::is_scalar(x_9)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_9;
}
lean::cnstr_set(x_19, 0, x_5);
lean::cnstr_set(x_19, 1, x_16);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
return x_20;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_7);
lean::dec(x_1);
x_23 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_9;
}
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
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
obj* _init_l_string_iterator_extract___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("");
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_string_iterator_extract___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; uint8 x_14; 
lean::inc(x_0);
x_3 = lean::string_iterator_fst(x_0);
x_4 = lean::string_iterator_snd(x_0);
lean::inc(x_1);
x_6 = lean::string_iterator_fst(x_1);
x_7 = lean::string_iterator_snd(x_1);
x_8 = l_list_reverse___rarg(x_3);
lean::inc(x_4);
x_10 = l_list_append___rarg(x_8, x_4);
x_11 = l_list_reverse___rarg(x_6);
lean::inc(x_7);
x_13 = l_list_append___rarg(x_11, x_7);
x_14 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_10, x_13);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_4);
x_17 = lean::box(0);
return x_17;
}
else
{
uint8 x_20; 
lean::inc(x_7);
lean::inc(x_4);
x_20 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_4, x_7);
if (x_20 == 0)
{
obj* x_21; 
x_21 = l_string_iterator_extract__core___main(x_4, x_7);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; 
lean::dec(x_21);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_26 = x_21;
}
x_27 = lean::string_mk(x_24);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
else
{
obj* x_31; 
lean::dec(x_7);
lean::dec(x_4);
x_31 = l_string_iterator_extract___main___closed__1;
lean::inc(x_31);
return x_31;
}
}
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
lean::inc(x_0);
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
uint8 x_10; 
lean::dec(x_5);
lean::dec(x_0);
x_10 = 0;
return x_10;
}
else
{
obj* x_11; obj* x_14; uint8 x_16; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_14 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
x_16 = lean::string_dec_eq(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
if (x_16 == 0)
{
uint8 x_19; 
x_19 = 0;
return x_19;
}
else
{
uint8 x_20; 
x_20 = 1;
return x_20;
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
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
x_11 = lean::string_push(x_3, x_0);
x_2 = x_8;
x_3 = x_11;
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
lean::dec(x_3);
lean::dec(x_1);
if (x_4 == 0)
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::string_append(x_0, x_3);
lean::dec(x_3);
x_0 = x_8;
x_1 = x_5;
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
obj* x_1; obj* x_3; 
x_1 = l_string_join___closed__1;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_string_join___spec__1(x_1, x_0);
return x_3;
}
}
obj* l_string_singleton(uint32 x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_string_join___closed__1;
lean::inc(x_1);
x_3 = lean::string_push(x_1, x_0);
return x_3;
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
x_8 = lean::string_data(x_3);
x_9 = l_list_map___main___at_string_intercalate___spec__1(x_5);
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
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::string_iterator_next(x_0);
x_0 = x_9;
x_1 = x_6;
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
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::string_iterator_prev(x_0);
x_0 = x_9;
x_1 = x_6;
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
lean::dec(x_2);
if (x_3 == 0)
{
uint32 x_5; uint8 x_6; 
x_5 = lean::string_iterator_curr(x_1);
x_6 = l_char_is__whitespace(x_5);
if (x_6 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_8);
lean::dec(x_0);
x_12 = lean::string_iterator_next(x_1);
x_0 = x_9;
x_1 = x_12;
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
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_6; uint32 x_7; uint8 x_8; 
lean::inc(x_1);
x_6 = lean::string_iterator_prev(x_1);
x_7 = lean::string_iterator_curr(x_6);
x_8 = l_char_is__whitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_6);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_1);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_12);
lean::dec(x_0);
x_0 = x_13;
x_1 = x_6;
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
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_13; 
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
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_8, x_11);
return x_13;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; uint8 x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_0);
x_14 = lean::string_iterator_has_next(x_1);
if (x_14 == 0)
{
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_7);
lean::dec(x_3);
return x_2;
}
else
{
obj* x_22; 
lean::dec(x_2);
x_22 = lean::box(0);
x_12 = x_22;
goto lbl_13;
}
lbl_13:
{
uint32 x_24; obj* x_25; obj* x_26; uint8 x_27; uint32 x_29; 
lean::dec(x_12);
x_24 = lean::string_iterator_curr(x_1);
x_25 = lean::mk_nat_obj(10u);
x_26 = lean::mk_nat_obj(55296u);
x_27 = lean::nat_dec_lt(x_25, x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(57343u);
x_32 = lean::nat_dec_lt(x_31, x_25);
lean::dec(x_31);
if (x_32 == 0)
{
uint32 x_35; 
lean::dec(x_25);
x_35 = lean::unbox_uint32(x_3);
x_29 = x_35;
goto lbl_30;
}
else
{
obj* x_36; uint8 x_37; 
x_36 = lean::mk_nat_obj(1114112u);
x_37 = lean::nat_dec_lt(x_25, x_36);
lean::dec(x_36);
if (x_37 == 0)
{
uint32 x_40; 
lean::dec(x_25);
x_40 = lean::unbox_uint32(x_3);
x_29 = x_40;
goto lbl_30;
}
else
{
uint32 x_41; 
x_41 = lean::unbox_uint32(x_25);
lean::dec(x_25);
x_29 = x_41;
goto lbl_30;
}
}
}
else
{
uint32 x_43; 
x_43 = lean::unbox_uint32(x_25);
lean::dec(x_25);
x_29 = x_43;
goto lbl_30;
}
lbl_30:
{
obj* x_45; obj* x_46; uint8 x_47; 
x_45 = lean::box_uint32(x_24);
x_46 = lean::box_uint32(x_29);
x_47 = lean::nat_dec_eq(x_45, x_46);
lean::dec(x_46);
lean::dec(x_45);
if (x_47 == 0)
{
obj* x_51; obj* x_52; obj* x_55; 
lean::dec(x_3);
x_51 = lean::string_iterator_next(x_1);
x_52 = lean::nat_add(x_7, x_9);
lean::dec(x_9);
lean::dec(x_7);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_5);
lean::cnstr_set(x_55, 1, x_52);
x_0 = x_10;
x_1 = x_51;
x_2 = x_55;
goto _start;
}
else
{
obj* x_58; obj* x_59; obj* x_62; 
lean::dec(x_7);
x_58 = lean::string_iterator_next(x_1);
x_59 = lean::nat_add(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_3);
x_0 = x_10;
x_1 = x_58;
x_2 = x_62;
goto _start;
}
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_3);
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
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_string_line__column___closed__1;
lean::inc(x_3);
x_5 = l___private_init_data_string_basic_3__line__column__aux___main(x_1, x_2, x_3);
return x_5;
}
}
obj* l_char_to__string(uint32 x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_string_join___closed__1;
lean::inc(x_1);
x_3 = lean::string_push(x_1, x_0);
return x_3;
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
obj* l___private_init_data_string_basic_4__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint32 x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_18; obj* x_19; uint8 x_20; obj* x_22; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::string_iterator_curr(x_0);
x_10 = lean::mk_nat_obj(10u);
x_11 = lean::nat_mul(x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
x_14 = lean::box_uint32(x_9);
x_15 = lean::nat_add(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
x_18 = lean::mk_nat_obj(48u);
x_19 = lean::mk_nat_obj(55296u);
x_20 = lean::nat_dec_lt(x_18, x_19);
lean::dec(x_19);
x_22 = lean::string_iterator_next(x_0);
if (x_20 == 0)
{
obj* x_23; uint8 x_24; 
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_18);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_27; 
lean::dec(x_18);
x_27 = lean::nat_sub(x_15, x_3);
lean::dec(x_3);
lean::dec(x_15);
x_0 = x_22;
x_1 = x_6;
x_2 = x_27;
goto _start;
}
else
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(1114112u);
x_32 = lean::nat_dec_lt(x_18, x_31);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_35; 
lean::dec(x_18);
x_35 = lean::nat_sub(x_15, x_3);
lean::dec(x_3);
lean::dec(x_15);
x_0 = x_22;
x_1 = x_6;
x_2 = x_35;
goto _start;
}
else
{
obj* x_40; 
lean::dec(x_3);
x_40 = lean::nat_sub(x_15, x_18);
lean::dec(x_18);
lean::dec(x_15);
x_0 = x_22;
x_1 = x_6;
x_2 = x_40;
goto _start;
}
}
}
else
{
obj* x_45; 
lean::dec(x_3);
x_45 = lean::nat_sub(x_15, x_18);
lean::dec(x_18);
lean::dec(x_15);
x_0 = x_22;
x_1 = x_6;
x_2 = x_45;
goto _start;
}
}
else
{
lean::dec(x_1);
lean::dec(x_3);
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
 l_string_has__lt = _init_l_string_has__lt();
 l_string_iterator_extract___main___closed__1 = _init_l_string_iterator_extract___main___closed__1();
 l_string_iterator_is__prefix__of__remaining = _init_l_string_iterator_is__prefix__of__remaining();
 l_string_inhabited = _init_l_string_inhabited();
 l_string_has__sizeof = _init_l_string_has__sizeof();
 l_string_has__append = _init_l_string_has__append();
 l_string_join___closed__1 = _init_l_string_join___closed__1();
 l_string_line__column___closed__1 = _init_l_string_line__column___closed__1();
}

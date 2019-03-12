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
usize l___private_init_data_string_basic_2__utf8__byte__size__aux(obj*, usize);
obj* l_string_iterator_prevn(obj*, obj*);
namespace lean {
obj* string_iterator_prev_to_string(obj*);
}
usize l___private_init_data_string_basic_2__utf8__byte__size__aux___main(obj*, usize);
uint32 l_string_front(obj*);
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main(obj*, usize, usize);
usize l_string_trim__left__aux___main(obj*, obj*, usize);
obj* l_string_trim__left___boxed(obj*);
uint8 l_char_is__whitespace(uint32);
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main___boxed(obj*, obj*, obj*);
obj* l_string_iterator_prev__to__string___boxed(obj*);
namespace lean {
obj* string_utf8_extract(obj*, usize, usize);
}
obj* l_string_pushn___boxed(obj*, obj*, obj*);
usize l_string_trim__right__aux(obj*, obj*, usize);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_string_has__lt;
obj* l___private_init_data_string_basic_9__to__nat__core___main(obj*, obj*, obj*);
obj* l_string_iterator_remaining___boxed(obj*);
obj* l_string_iterator_forward(obj*, obj*);
obj* l_string_decidable__eq;
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___main___boxed(obj*, obj*, obj*, obj*);
obj* l_string_line__column___closed__1;
obj* l_list_foldl___main___at_string_join___spec__1___boxed(obj*, obj*);
obj* l_string_singleton(uint32);
obj* l_string_pushn(obj*, uint32, obj*);
obj* l_list_as__string(obj*);
obj* l___private_init_data_string_basic_4__utf8__set__aux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_string_iterator_forward___main(obj*, obj*);
obj* l_string_iterator_has__next___boxed(obj*);
obj* l_string_trim__right__aux___boxed(obj*, obj*, obj*);
obj* l_nat_repeat__core___main___at_string_pushn___spec__1(uint32, obj*, obj*, obj*);
obj* l_string_iterator_extract__core(obj*, obj*);
obj* l_string_back___boxed(obj*);
obj* l_string_trim___boxed(obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
namespace lean {
usize string_utf8_next(obj*, usize);
}
obj* l___private_init_data_string_basic_5__utf8__prev__aux___main___boxed(obj*, obj*, obj*);
obj* l_string_trim__right___boxed(obj*);
usize l___private_init_data_string_basic_5__utf8__prev__aux(obj*, usize, usize);
namespace lean {
usize string_utf8_byte_size(obj*);
}
obj* l_string_singleton___boxed(obj*);
obj* l_string_bsize___boxed(obj*);
usize l___private_init_data_string_basic_1__csize(uint32);
namespace lean {
obj* string_length(obj*);
}
obj* l_string_front___boxed(obj*);
usize l_string_utf8__begin;
uint8 l_string_is__empty(obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l___private_init_data_string_basic_9__to__nat__core(obj*, obj*, obj*);
namespace lean {
obj* string_iterator_set_curr(obj*, uint32);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_string_iterator_insert___boxed(obj*, obj*);
obj* l_string_pop__back(obj*);
usize l_string_trim__left__aux(obj*, obj*, usize);
uint32 l___private_init_data_string_basic_3__utf8__get__aux___main(obj*, usize, usize);
obj* l_string_intercalate(obj*, obj*);
obj* l___private_init_data_string_basic_3__utf8__get__aux___main___boxed(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_lt(obj*, obj*);
}
namespace lean {
usize string_utf8_prev(obj*, usize);
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
obj* l_string_utf8__begin___boxed;
namespace lean {
obj* string_data(obj*);
}
obj* l_string_append___boxed(obj*, obj*);
obj* l_string_str(obj*, uint32);
obj* l_string_to__nat(obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l___private_init_data_string_basic_8__line__column__aux(obj*, obj*, obj*);
obj* l_string_utf8__at__end___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_9__to__nat__core___main___closed__1;
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081(obj*, usize, usize, usize);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
obj* string_iterator_remaining_to_string(obj*);
}
obj* l_string_line__column(obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8__set__aux___boxed(obj*, obj*, obj*, obj*);
obj* l_string_iterator_nextn___main(obj*, obj*);
obj* l_string_trim__right__aux___main___boxed(obj*, obj*, obj*);
obj* l___private_init_data_string_basic_4__utf8__set__aux(uint32, obj*, usize, usize);
obj* l_string_length___boxed(obj*);
obj* l_string_iterator_to__string___boxed(obj*);
obj* l_string_iterator_remove___boxed(obj*, obj*);
obj* l___private_init_data_string_basic_2__utf8__byte__size__aux___main___boxed(obj*, obj*);
obj* l_string_join___closed__1;
uint32 l___private_init_data_string_basic_3__utf8__get__aux(obj*, usize, usize);
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l_string_iterator_offset___boxed(obj*);
obj* l___private_init_data_string_basic_8__line__column__aux___main(obj*, obj*, obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_string_utf8__get___boxed(obj*, obj*);
obj* l_string_trim__left__aux___main___boxed(obj*, obj*, obj*);
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
obj* l_string_utf8__byte__size___boxed(obj*);
namespace lean {
obj* string_mk(obj*);
}
usize l___private_init_data_string_basic_5__utf8__prev__aux___main(obj*, usize, usize);
obj* l_string_inhabited;
obj* l_string_join(obj*);
obj* l___private_init_data_string_basic_2__utf8__byte__size__aux___boxed(obj*, obj*);
uint8 l_string_iterator_decidable__rel(obj*, obj*);
obj* l_string_push___boxed(obj*, obj*);
obj* l_string_dec__eq___boxed(obj*, obj*);
obj* l_string_mk__iterator___boxed(obj*);
obj* l_string_iterator_decidable__rel___boxed(obj*, obj*);
obj* l_string_utf8__prev___boxed(obj*, obj*);
obj* l_string_utf8__next___boxed(obj*, obj*);
obj* l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1___boxed(obj*, obj*);
obj* l_string_iterator_nextn(obj*, obj*);
obj* l___private_init_data_string_basic_1__csize___boxed(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_string_trim__right(obj*);
obj* l_string_iterator_extract__core___main(obj*, obj*);
uint32 l_char_utf8__size(uint32);
namespace lean {
obj* string_iterator_insert(obj*, obj*);
}
obj* l___private_init_data_string_basic_3__utf8__get__aux___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_utf8_set(obj*, usize, uint32);
}
obj* l_char_to__string(uint32);
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
usize usize_of_nat(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
usize l_string_bsize(obj*);
obj* l_list_map___main___at_string_intercalate___spec__1(obj*);
obj* l_string_has__sizeof;
obj* l_string_to__list(obj*);
obj* l_string_trim(obj*);
obj* l_string_utf8__set___boxed(obj*, obj*, obj*);
uint8 l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(obj*, obj*);
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___boxed(obj*, obj*, obj*);
obj* l_string_iterator_set__curr___boxed(obj*, obj*);
obj* l_nat_repeat__core___main___at_string_pushn___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_string_extract___boxed(obj*, obj*, obj*);
obj* l_string_iterator_prev___boxed(obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_string_is__empty___boxed(obj*);
obj* l___private_init_data_string_basic_4__utf8__set__aux___main(uint32, obj*, usize, usize);
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082(obj*, usize, usize);
namespace lean {
uint8 string_iterator_has_prev(obj*);
}
obj* l_string_iterator_to__end___boxed(obj*);
obj* l_string_iterator_extract___boxed(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_string_trim__left(obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
namespace lean {
uint32 string_utf8_get(obj*, usize);
}
obj* l_string_str___boxed(obj*, obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, usize);
}
obj* l_string_iterator_remaining__to__string___boxed(obj*);
usize l_string_trim__right__aux___main(obj*, obj*, usize);
namespace lean {
obj* string_iterator_to_string(obj*);
}
obj* l_string_iterator_has__prev___boxed(obj*);
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___main(obj*, usize, usize, usize);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_string_basic_5__utf8__prev__aux___boxed(obj*, obj*, obj*);
obj* l_string_dec__lt___boxed(obj*, obj*);
obj* l_string_trim__left__aux___boxed(obj*, obj*, obj*);
obj* l_string_join___boxed(obj*);
obj* l_string_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::string_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_string_length___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_length(x_0);
lean::dec(x_0);
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
lean::dec(x_1);
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
usize l___private_init_data_string_basic_1__csize(uint32 x_0) {
_start:
{
uint32 x_1; usize x_2; 
x_1 = l_char_utf8__size(x_0);
x_2 = x_1;
return x_2;
}
}
obj* l___private_init_data_string_basic_1__csize___boxed(obj* x_0) {
_start:
{
uint32 x_1; usize x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l___private_init_data_string_basic_1__csize(x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
usize l___private_init_data_string_basic_2__utf8__byte__size__aux___main(obj* x_0, usize x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_3; uint32 x_4; usize x_5; usize x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::unbox_uint32(x_2);
x_5 = l___private_init_data_string_basic_1__csize(x_4);
x_6 = x_1 + x_5;
x_0 = x_3;
x_1 = x_6;
goto _start;
}
}
}
obj* l___private_init_data_string_basic_2__utf8__byte__size__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_data_string_basic_2__utf8__byte__size__aux___main(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
usize l___private_init_data_string_basic_2__utf8__byte__size__aux(obj* x_0, usize x_1) {
_start:
{
usize x_2; 
x_2 = l___private_init_data_string_basic_2__utf8__byte__size__aux___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_data_string_basic_2__utf8__byte__size__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = l___private_init_data_string_basic_2__utf8__byte__size__aux(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_string_utf8__byte__size___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
usize _init_l_string_utf8__begin() {
_start:
{
usize x_0; 
x_0 = 0;
return x_0;
}
}
obj* _init_l_string_utf8__begin___boxed() {
_start:
{
usize x_0; obj* x_1; 
x_0 = l_string_utf8__begin;
x_1 = lean::box_size_t(x_0);
return x_1;
}
}
uint32 l___private_init_data_string_basic_3__utf8__get__aux___main(obj* x_0, usize x_1, usize x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint32 x_3; 
x_3 = 65;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
x_6 = x_1 == x_2;
if (x_6 == 0)
{
uint32 x_7; usize x_8; usize x_9; 
x_7 = lean::unbox_uint32(x_4);
x_8 = l___private_init_data_string_basic_1__csize(x_7);
x_9 = x_1 + x_8;
x_0 = x_5;
x_1 = x_9;
goto _start;
}
else
{
uint32 x_11; 
x_11 = lean::unbox_uint32(x_4);
return x_11;
}
}
}
}
obj* l___private_init_data_string_basic_3__utf8__get__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; uint32 x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_3__utf8__get__aux___main(x_0, x_3, x_4);
x_6 = lean::box_uint32(x_5);
lean::dec(x_0);
return x_6;
}
}
uint32 l___private_init_data_string_basic_3__utf8__get__aux(obj* x_0, usize x_1, usize x_2) {
_start:
{
uint32 x_3; 
x_3 = l___private_init_data_string_basic_3__utf8__get__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_3__utf8__get__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; uint32 x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_3__utf8__get__aux(x_0, x_3, x_4);
x_6 = lean::box_uint32(x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_string_utf8__get___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; uint32 x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_get(x_0, x_2);
x_4 = lean::box_uint32(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_data_string_basic_4__utf8__set__aux___main(uint32 x_0, obj* x_1, usize x_2, usize x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = x_2 == x_3;
if (x_9 == 0)
{
uint32 x_10; usize x_11; usize x_12; obj* x_13; obj* x_14; 
x_10 = lean::unbox_uint32(x_4);
x_11 = l___private_init_data_string_basic_1__csize(x_10);
x_12 = x_2 + x_11;
x_13 = l___private_init_data_string_basic_4__utf8__set__aux___main(x_0, x_6, x_12, x_3);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_4);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
x_16 = lean::box_uint32(x_0);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_8;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_6);
return x_17;
}
}
}
}
obj* l___private_init_data_string_basic_4__utf8__set__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_uint32(x_0);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_4__utf8__set__aux___main(x_4, x_1, x_5, x_6);
return x_7;
}
}
obj* l___private_init_data_string_basic_4__utf8__set__aux(uint32 x_0, obj* x_1, usize x_2, usize x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_4__utf8__set__aux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_4__utf8__set__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_uint32(x_0);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_4__utf8__set__aux(x_4, x_1, x_5, x_6);
return x_7;
}
}
obj* l_string_utf8__set___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; uint32 x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_uint32(x_2);
x_5 = lean::string_utf8_set(x_0, x_3, x_4);
return x_5;
}
}
obj* l_string_utf8__next___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_next(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
usize l___private_init_data_string_basic_5__utf8__prev__aux___main(obj* x_0, usize x_1, usize x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
usize x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint32 x_6; usize x_7; usize x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
x_6 = lean::unbox_uint32(x_4);
x_7 = l___private_init_data_string_basic_1__csize(x_6);
x_8 = x_1 + x_7;
x_9 = x_8 == x_2;
if (x_9 == 0)
{
x_0 = x_5;
x_1 = x_8;
goto _start;
}
else
{
return x_1;
}
}
}
}
obj* l___private_init_data_string_basic_5__utf8__prev__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_5__utf8__prev__aux___main(x_0, x_3, x_4);
x_6 = lean::box_size_t(x_5);
lean::dec(x_0);
return x_6;
}
}
usize l___private_init_data_string_basic_5__utf8__prev__aux(obj* x_0, usize x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = l___private_init_data_string_basic_5__utf8__prev__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_5__utf8__prev__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_5__utf8__prev__aux(x_0, x_3, x_4);
x_6 = lean::box_size_t(x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_string_utf8__prev___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; usize x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_prev(x_0, x_2);
x_4 = lean::box_size_t(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_string_utf8__at__end___boxed(obj* x_0, obj* x_1) {
_start:
{
usize x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox_size_t(x_1);
x_3 = lean::string_utf8_at_end(x_0, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main(obj* x_0, usize x_1, usize x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = x_1 == x_2;
if (x_8 == 0)
{
uint32 x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; 
x_9 = lean::unbox_uint32(x_3);
x_10 = l___private_init_data_string_basic_1__csize(x_9);
x_11 = x_1 + x_10;
x_12 = l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main(x_5, x_11, x_2);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_3);
x_17 = lean::box(0);
return x_17;
}
}
}
}
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main(x_0, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082(obj* x_0, usize x_1, usize x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = l___private_init_data_string_basic_6__utf8__extract__aux_u_2082(x_0, x_3, x_4);
return x_5;
}
}
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___main(obj* x_0, usize x_1, usize x_2, usize x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_4; obj* x_6; uint8 x_8; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = x_1 == x_2;
if (x_8 == 0)
{
uint32 x_10; usize x_11; usize x_12; 
lean::dec(x_0);
x_10 = lean::unbox_uint32(x_4);
x_11 = l___private_init_data_string_basic_1__csize(x_10);
x_12 = x_1 + x_11;
x_0 = x_6;
x_1 = x_12;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_6);
lean::dec(x_4);
x_16 = l___private_init_data_string_basic_6__utf8__extract__aux_u_2082___main(x_0, x_1, x_3);
return x_16;
}
}
}
}
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_size_t(x_1);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___main(x_0, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081(obj* x_0, usize x_1, usize x_2, usize x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_string_basic_7__utf8__extract__aux_u_2081___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; usize x_5; usize x_6; obj* x_7; 
x_4 = lean::unbox_size_t(x_1);
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::unbox_size_t(x_3);
x_7 = l___private_init_data_string_basic_7__utf8__extract__aux_u_2081(x_0, x_4, x_5, x_6);
return x_7;
}
}
obj* l_string_extract___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_1);
x_4 = lean::unbox_size_t(x_2);
x_5 = lean::string_utf8_extract(x_0, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
usize l_string_bsize(obj* x_0) {
_start:
{
usize x_1; 
x_1 = lean::string_utf8_byte_size(x_0);
return x_1;
}
}
obj* l_string_bsize___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_string_bsize(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
usize l_string_trim__left__aux___main(obj* x_0, obj* x_1, usize x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
usize x_5; uint8 x_6; 
x_5 = lean::string_utf8_byte_size(x_0);
x_6 = x_5 <= x_2;
if (x_6 == 0)
{
uint32 x_7; uint8 x_8; 
x_7 = lean::string_utf8_get(x_0, x_2);
x_8 = l_char_is__whitespace(x_7);
if (x_8 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_10; obj* x_11; usize x_13; usize x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_1);
x_13 = l___private_init_data_string_basic_1__csize(x_7);
x_14 = x_2 + x_13;
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_string_trim__left__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_string_trim__left__aux___main(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
usize l_string_trim__left__aux(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = l_string_trim__left__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_string_trim__left__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_string_trim__left__aux(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_string_trim__left(obj* x_0) {
_start:
{
usize x_1; obj* x_2; usize x_3; usize x_4; uint8 x_5; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::usize_to_nat(x_1);
x_3 = 0;
x_4 = l_string_trim__left__aux___main(x_0, x_2, x_3);
x_5 = x_4 == x_3;
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::string_utf8_extract(x_0, x_4, x_1);
return x_6;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l_string_trim__left___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_trim__left(x_0);
lean::dec(x_0);
return x_1;
}
}
usize l_string_trim__right__aux___main(obj* x_0, obj* x_1, usize x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
usize x_5; uint8 x_6; 
x_5 = 0;
x_6 = x_2 == x_5;
if (x_6 == 0)
{
usize x_7; uint32 x_8; uint8 x_9; 
x_7 = lean::string_utf8_prev(x_0, x_2);
x_8 = lean::string_utf8_get(x_0, x_7);
x_9 = l_char_is__whitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_1, x_11);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_7;
goto _start;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l_string_trim__right__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_string_trim__right__aux___main(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
usize l_string_trim__right__aux(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = l_string_trim__right__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_string_trim__right__aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_string_trim__right__aux(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_string_trim__right(obj* x_0) {
_start:
{
usize x_1; obj* x_2; usize x_3; uint8 x_4; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::usize_to_nat(x_1);
x_3 = l_string_trim__right__aux___main(x_0, x_2, x_1);
x_4 = x_3 == x_1;
if (x_4 == 0)
{
usize x_5; obj* x_6; 
x_5 = 0;
x_6 = lean::string_utf8_extract(x_0, x_5, x_3);
return x_6;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l_string_trim__right___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_trim__right(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_string_trim(obj* x_0) {
_start:
{
usize x_1; obj* x_2; usize x_3; usize x_5; usize x_6; uint8 x_7; 
x_1 = lean::string_utf8_byte_size(x_0);
x_2 = lean::usize_to_nat(x_1);
x_3 = 0;
lean::inc(x_2);
x_5 = l_string_trim__left__aux___main(x_0, x_2, x_3);
x_6 = l_string_trim__right__aux___main(x_0, x_2, x_1);
x_7 = x_5 == x_3;
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::string_utf8_extract(x_0, x_5, x_6);
return x_8;
}
else
{
uint8 x_9; 
x_9 = x_6 == x_1;
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::string_utf8_extract(x_0, x_5, x_6);
return x_10;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
}
obj* l_string_trim___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_trim(x_0);
lean::dec(x_0);
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
lean::dec(x_0);
return x_1;
}
}
obj* l_string_iterator_offset___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_offset(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_string_iterator_curr___boxed(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = lean::string_iterator_curr(x_0);
x_2 = lean::box_uint32(x_1);
lean::dec(x_0);
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
lean::dec(x_0);
return x_2;
}
}
obj* l_string_iterator_has__prev___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::string_iterator_has_prev(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_string_iterator_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_iterator_insert(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_string_iterator_remove___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_iterator_remove(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_string_iterator_to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_to_string(x_0);
lean::dec(x_0);
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
lean::dec(x_0);
return x_1;
}
}
obj* l_string_iterator_prev__to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_prev_to_string(x_0);
lean::dec(x_0);
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
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
lean::dec(x_0);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; uint32 x_17; uint32 x_18; uint8 x_19; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::unbox_uint32(x_7);
x_18 = lean::unbox_uint32(x_12);
x_19 = x_17 == x_18;
if (x_19 == 0)
{
uint8 x_22; 
lean::dec(x_14);
lean::dec(x_9);
x_22 = 0;
return x_22;
}
else
{
uint8 x_23; 
x_23 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_9, x_14);
if (x_23 == 0)
{
uint8 x_24; 
x_24 = 0;
return x_24;
}
else
{
uint8 x_25; 
x_25 = 1;
return x_25;
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
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_12; uint8 x_13; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
lean::dec(x_5);
x_12 = lean::string_iterator_remaining_to_string(x_0);
x_13 = lean::string_dec_eq(x_9, x_12);
lean::dec(x_12);
lean::dec(x_9);
if (x_13 == 0)
{
uint8 x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8 x_17; 
x_17 = 1;
return x_17;
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
lean::dec(x_0);
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
lean::dec(x_2);
return x_4;
}
}
obj* l_nat_repeat__core___main___at_string_pushn___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_nat_repeat__core___main___at_string_pushn___spec__1(x_4, x_1, x_2, x_3);
lean::dec(x_1);
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
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::string_length(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* l_string_is__empty___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_string_is__empty(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
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
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::string_append(x_0, x_2);
x_0 = x_4;
x_1 = x_3;
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
obj* l_list_foldl___main___at_string_join___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldl___main___at_string_join___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_string_join___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_join(x_0);
lean::dec(x_0);
return x_1;
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
obj* l___private_init_data_string_basic_8__line__column__aux___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_14; obj* x_15; obj* x_16; uint32 x_18; uint32 x_19; uint8 x_20; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_14 = x_2;
} else {
 lean::dec(x_2);
 x_14 = lean::box(0);
}
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
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_14;
}
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
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_14;
}
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
obj* l___private_init_data_string_basic_8__line__column__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_8__line__column__aux___main(x_0, x_1, x_2);
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
x_4 = l___private_init_data_string_basic_8__line__column__aux___main(x_1, x_2, x_3);
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
obj* _init_l___private_init_data_string_basic_9__to__nat__core___main___closed__1() {
_start:
{
uint32 x_0; obj* x_1; 
x_0 = 48;
x_1 = lean::uint32_to_nat(x_0);
return x_1;
}
}
obj* l___private_init_data_string_basic_9__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2) {
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
x_16 = l___private_init_data_string_basic_9__to__nat__core___main___closed__1;
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
obj* l___private_init_data_string_basic_9__to__nat__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_string_basic_9__to__nat__core___main(x_0, x_1, x_2);
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
x_6 = l___private_init_data_string_basic_9__to__nat__core___main(x_2, x_3, x_5);
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
 l_string_utf8__begin = _init_l_string_utf8__begin();
 l_string_utf8__begin___boxed = _init_l_string_utf8__begin___boxed();
lean::mark_persistent(l_string_utf8__begin___boxed);
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
 l___private_init_data_string_basic_9__to__nat__core___main___closed__1 = _init_l___private_init_data_string_basic_9__to__nat__core___main___closed__1();
lean::mark_persistent(l___private_init_data_string_basic_9__to__nat__core___main___closed__1);
}

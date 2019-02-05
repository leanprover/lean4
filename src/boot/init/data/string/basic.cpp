// Lean compiler output
// Module: init.data.string.basic
// Imports: init.data.list.basic init.data.char.basic init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_string_iterator_prevn___main(obj*, obj*);
obj* l_string_iterator_decidable__rel(obj*, obj*);
obj* l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(obj*, obj*);
obj* l_nat_repeat___main___at_string_pushn___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_615858501__trim__right__aux(obj*, obj*);
obj* l_string_length___main(obj*);
obj* l_string_to__nat(obj*);
obj* l_string_pushn(obj*, unsigned, obj*);
obj* l_list_intercalate___rarg(obj*, obj*);
obj* l_string_iterator_offset___main(obj*);
obj* l_string_trim(obj*);
obj* l_string_iterator_curr___main(obj*);
obj* l_string_iterator_prev___main(obj*);
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l_string_join(obj*);
obj* l_string_iterator_nextn___main(obj*, obj*);
obj* l_string_append___main(obj*, obj*);
obj* l___private_3344645481__to__nat__core(obj*, obj*, obj*);
unsigned char l_string_iterator_has__prev___main(obj*);
obj* l___private_104996535__line__column__aux___main(obj*, obj*, obj*);
unsigned l_string_front(obj*);
obj* l_string_iterator_next___main(obj*);
obj* l___private_3868098097__trim__left__aux___main(obj*, obj*);
obj* l_string_iterator_has__next___main___boxed(obj*);
obj* l_string_iterator_extract__core___main(obj*, obj*);
obj* l_string_has__lt;
obj* l_string_iterator_remaining__to__string___main(obj*);
obj* l___private_3344645481__to__nat__core___main(obj*, obj*, obj*);
obj* l_string_singleton___boxed(obj*);
obj* l_string_has__append;
obj* l_string_iterator_has__prev___main___boxed(obj*);
obj* l_string_front___boxed(obj*);
obj* l___private_3868098097__trim__left__aux(obj*, obj*);
obj* l_string_iterator_curr___boxed(obj*);
obj* l_list_as__string(obj*);
extern obj* l_char_inhabited;
obj* l_list_drop___main___rarg(obj*, obj*);
obj* l_string_iterator_is__prefix__of__remaining;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_string_iterator_forward___main(obj*, obj*);
obj* l_string_mk__iterator___main(obj*);
obj* l_string_iterator_remaining___main(obj*);
obj* l_string_str___boxed(obj*, obj*);
obj* l_string_iterator_insert___main(obj*, obj*);
obj* l_string_push___main___boxed(obj*, obj*);
obj* l_string_backn(obj*, obj*);
obj* l_string_iterator_extract___main(obj*, obj*);
unsigned char l_string_is__empty(obj*);
obj* l_string_iterator_has__prev___boxed(obj*);
obj* l_nat_repeat___main___at_string_pushn___spec__1(obj*, unsigned, obj*);
obj* l_string_intercalate(obj*, obj*);
obj* l_string_iterator_set__curr___main___boxed(obj*, obj*);
obj* l_char_to__string___boxed(obj*);
obj* l_string_to__list(obj*);
obj* l_string_iterator_forward(obj*, obj*);
obj* l_string_has__sizeof;
obj* l_string_trim__left(obj*);
obj* l_string_iterator_extract__core(obj*, obj*);
obj* l_string_line__column___closed__1;
obj* l_string_back___boxed(obj*);
obj* l_string_iterator_remove___main(obj*, obj*);
obj* l_string_inhabited;
obj* l_list_reverse___rarg(obj*);
obj* l___private_615858501__trim__right__aux___main(obj*, obj*);
obj* l_string_join___closed__1;
obj* l_string_line__column(obj*, obj*);
obj* l_string_iterator_to__string___main(obj*);
obj* l_string_iterator_extract___main___closed__1;
obj* l_string_iterator_has__next___boxed(obj*);
obj* l_list_map___main___at_string_intercalate___spec__1(obj*);
obj* l_string_iterator_to__end___main(obj*);
obj* l_list_append___main___rarg(obj*, obj*);
unsigned char l_char_is__whitespace(unsigned);
obj* l_string_iterator_nextn(obj*, obj*);
obj* l_char_to__string(unsigned);
obj* l_string_pushn___boxed(obj*, obj*, obj*);
obj* l_string_singleton(unsigned);
obj* l_string_trim__right(obj*);
obj* l_string_iterator_prevn(obj*, obj*);
obj* l_string_iterator_set__curr___main(obj*, unsigned);
obj* l_string_str(obj*, unsigned);
obj* l_string_iterator_set__curr___boxed(obj*, obj*);
unsigned char l_string_iterator_has__next___main(obj*);
obj* l_string_is__empty___boxed(obj*);
unsigned l_string_back(obj*);
obj* l___private_104996535__line__column__aux(obj*, obj*, obj*);
obj* l_string_push___boxed(obj*, obj*);
obj* l_list_length___main___rarg(obj*);
obj* l_string_popn__back(obj*, obj*);
obj* l_string_push___main(obj*, unsigned);
obj* l_string_iterator_prev__to__string___main(obj*);
obj* l_string_pop__back(obj*);
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
obj* l_string_length___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::string_data(x_0);
x_2 = l_list_length___main___rarg(x_1);
return x_2;
}
}
obj* l_string_push___main(obj* x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_data(x_0);
x_3 = lean::box(0);
x_4 = lean::box_uint32(x_1);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = l_list_append___main___rarg(x_2, x_5);
x_7 = lean::string_mk(x_6);
return x_7;
}
}
obj* l_string_push___main___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_string_push___main(x_0, x_2);
return x_3;
}
}
obj* l_string_push___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
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
x_4 = l_list_append___main___rarg(x_2, x_3);
x_5 = lean::string_mk(x_4);
return x_5;
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
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_string_iterator_remaining___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_3 = l_list_length___main___rarg(x_1);
return x_3;
}
}
obj* l_string_iterator_offset___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::string_iterator_fst(x_0);
lean::dec(x_0);
x_3 = l_list_length___main___rarg(x_1);
return x_3;
}
}
obj* l_string_iterator_curr___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_char_inhabited;
lean::inc(x_4);
return x_4;
}
else
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
return x_6;
}
}
}
obj* l_string_iterator_curr___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = lean::string_iterator_curr(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
obj* l_string_iterator_set__curr___main(obj* x_0, unsigned x_1) {
_start:
{
obj* x_2; 
x_2 = lean::string_iterator_snd(x_0);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
return x_0;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_6 = x_2;
}
x_7 = lean::string_iterator_fst(x_0);
lean::dec(x_0);
x_9 = lean::box_uint32(x_1);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_4);
x_11 = lean::string_iterator_mk(x_7, x_10);
lean::dec(x_10);
lean::dec(x_7);
return x_11;
}
}
}
obj* l_string_iterator_set__curr___main___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_string_iterator_set__curr___main(x_0, x_2);
return x_3;
}
}
obj* l_string_iterator_set__curr___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = lean::string_iterator_set_curr(x_0, x_2);
return x_3;
}
}
obj* l_string_iterator_next___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_snd(x_0);
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::string_iterator_fst(x_0);
lean::dec(x_0);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::string_iterator_mk(x_10, x_5);
lean::dec(x_5);
lean::dec(x_10);
return x_11;
}
}
}
obj* l_string_iterator_prev___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_fst(x_0);
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
}
x_8 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::string_iterator_mk(x_5, x_10);
lean::dec(x_10);
lean::dec(x_5);
return x_11;
}
}
}
unsigned char l_string_iterator_has__next___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_4; 
lean::dec(x_1);
x_4 = 0;
return x_4;
}
else
{
unsigned char x_6; 
lean::dec(x_1);
x_6 = 1;
return x_6;
}
}
}
obj* l_string_iterator_has__next___main___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_string_iterator_has__next___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_string_iterator_has__next___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::string_iterator_has_next(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned char l_string_iterator_has__prev___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::string_iterator_fst(x_0);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_4; 
lean::dec(x_1);
x_4 = 0;
return x_4;
}
else
{
unsigned char x_6; 
lean::dec(x_1);
x_6 = 1;
return x_6;
}
}
}
obj* l_string_iterator_has__prev___main___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_string_iterator_has__prev___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_string_iterator_has__prev___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = lean::string_iterator_has_prev(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_string_iterator_insert___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::string_iterator_fst(x_0);
x_3 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_5 = lean::string_data(x_1);
x_6 = l_list_append___main___rarg(x_5, x_3);
x_7 = lean::string_iterator_mk(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_string_iterator_remove___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_fst(x_0);
x_3 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_5 = l_list_drop___main___rarg(x_1, x_3);
x_6 = lean::string_iterator_mk(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_string_iterator_to__string___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::string_iterator_fst(x_0);
x_2 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_4 = l_list_reverse___rarg(x_1);
x_5 = l_list_append___main___rarg(x_4, x_2);
x_6 = lean::string_mk(x_5);
return x_6;
}
}
obj* l_string_iterator_forward___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_10 = lean::string_iterator_next(x_0);
x_0 = x_10;
x_1 = x_7;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
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
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::string_iterator_fst(x_0);
x_2 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_4 = l_list_reverse___rarg(x_2);
x_5 = l_list_append___main___rarg(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::string_iterator_mk(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_string_iterator_remaining__to__string___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_3 = lean::string_mk(x_1);
return x_3;
}
}
obj* l_string_iterator_prev__to__string___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = lean::string_iterator_fst(x_0);
lean::dec(x_0);
x_3 = l_list_reverse___rarg(x_1);
x_4 = lean::string_mk(x_3);
return x_4;
}
}
obj* l_string_iterator_extract__core___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; 
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
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; 
lean::dec(x_12);
x_14 = l_string_iterator_extract__core___main(x_7, x_1);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_7;
goto _start;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_19 = x_14;
}
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_17);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_7);
lean::dec(x_12);
lean::dec(x_1);
x_25 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_9;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
}
}
obj* l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(1);
return x_4;
}
else
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::box(0);
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
obj* x_15; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_1);
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_21; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::nat_dec_eq(x_7, x_16);
lean::dec(x_16);
lean::dec(x_7);
if (lean::obj_tag(x_21) == 0)
{
obj* x_27; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_9);
x_27 = lean::box(0);
return x_27;
}
else
{
lean::dec(x_21);
x_0 = x_9;
x_1 = x_18;
goto _start;
}
}
}
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
obj* l_string_iterator_extract___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_2 = lean::string_iterator_fst(x_0);
x_3 = lean::string_iterator_snd(x_0);
lean::dec(x_0);
x_5 = lean::string_iterator_fst(x_1);
x_6 = lean::string_iterator_snd(x_1);
lean::dec(x_1);
x_8 = l_list_reverse___rarg(x_2);
lean::inc(x_3);
x_10 = l_list_append___main___rarg(x_8, x_3);
x_11 = l_list_reverse___rarg(x_5);
lean::inc(x_6);
x_13 = l_list_append___main___rarg(x_11, x_6);
x_14 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_10, x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; 
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_3);
x_18 = lean::box(0);
return x_18;
}
else
{
obj* x_22; 
lean::dec(x_14);
lean::inc(x_6);
lean::inc(x_3);
x_22 = l_list_has__dec__eq___main___at_string_iterator_extract__core___main___spec__1(x_3, x_6);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; 
lean::dec(x_22);
x_24 = l_string_iterator_extract__core___main(x_3, x_6);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; 
lean::dec(x_24);
x_26 = lean::box(0);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_29 = x_24;
}
x_30 = lean::string_mk(x_27);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
else
{
obj* x_35; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_22);
x_35 = l_string_iterator_extract___main___closed__1;
lean::inc(x_35);
return x_35;
}
}
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
obj* _init_l_string_iterator_is__prefix__of__remaining() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_string_iterator_decidable__rel(obj* x_0, obj* x_1) {
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
obj* x_10; 
lean::dec(x_5);
lean::dec(x_0);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_16; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_14 = lean::string_iterator_remaining_to_string(x_0);
lean::dec(x_0);
x_16 = lean::string_dec_eq(x_11, x_14);
lean::dec(x_14);
lean::dec(x_11);
return x_16;
}
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::string_length), 1, 0);
return x_0;
}
}
obj* _init_l_string_has__append() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::string_append), 2, 0);
return x_0;
}
}
obj* l_string_str(obj* x_0, unsigned x_1) {
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
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_string_str(x_0, x_2);
return x_3;
}
}
obj* l_string_pushn(obj* x_0, unsigned x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_nat_repeat___main___at_string_pushn___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_nat_repeat___main___at_string_pushn___spec__1(obj* x_0, unsigned x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
x_11 = l_nat_repeat___main___at_string_pushn___spec__1(x_0, x_1, x_8);
x_12 = lean::string_push(x_11, x_1);
return x_12;
}
else
{
lean::dec(x_4);
lean::dec(x_2);
return x_0;
}
}
}
obj* l_string_pushn___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_string_pushn(x_0, x_3, x_2);
return x_4;
}
}
obj* l_nat_repeat___main___at_string_pushn___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_nat_repeat___main___at_string_pushn___spec__1(x_0, x_3, x_2);
return x_4;
}
}
unsigned char l_string_is__empty(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = lean::string_length(x_0);
lean::dec(x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
lean::dec(x_3);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_8; 
lean::dec(x_4);
x_8 = 0;
return x_8;
}
else
{
unsigned char x_10; 
lean::dec(x_4);
x_10 = 1;
return x_10;
}
}
}
obj* l_string_is__empty___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = l_string_is__empty(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
unsigned l_string_front(obj* x_0) {
_start:
{
obj* x_1; unsigned x_2; 
x_1 = lean::string_mk_iterator(x_0);
x_2 = lean::string_iterator_curr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_string_front___boxed(obj* x_0) {
_start:
{
unsigned x_1; obj* x_2; 
x_1 = l_string_front(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
}
}
unsigned l_string_back(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; unsigned x_4; 
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
unsigned x_1; obj* x_2; 
x_1 = l_string_back(x_0);
x_2 = lean::box_uint32(x_1);
return x_2;
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
obj* _init_l_string_join___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
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
obj* l_string_singleton(unsigned x_0) {
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
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_string_singleton(x_1);
return x_2;
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
obj* l_string_iterator_nextn___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_10 = lean::string_iterator_next(x_0);
x_0 = x_10;
x_1 = x_7;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
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
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_10 = lean::string_iterator_prev(x_0);
x_0 = x_10;
x_1 = x_7;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
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
obj* l___private_3868098097__trim__left__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
unsigned x_6; unsigned char x_7; 
lean::dec(x_3);
x_6 = lean::string_iterator_curr(x_1);
x_7 = l_char_is__whitespace(x_6);
if (x_7 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_9; obj* x_10; obj* x_13; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_next(x_1);
x_0 = x_10;
x_1 = x_13;
goto _start;
}
}
else
{
lean::dec(x_0);
lean::dec(x_3);
return x_1;
}
}
}
obj* l___private_3868098097__trim__left__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_3868098097__trim__left__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_string_trim__left(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = l___private_3868098097__trim__left__aux___main(x_1, x_2);
x_4 = lean::string_iterator_remaining_to_string(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_615858501__trim__right__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_0, x_2);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; unsigned x_8; unsigned char x_9; 
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::string_iterator_prev(x_1);
x_8 = lean::string_iterator_curr(x_7);
x_9 = l_char_is__whitespace(x_8);
if (x_9 == 0)
{
lean::dec(x_7);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_1);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_0 = x_14;
x_1 = x_7;
goto _start;
}
}
else
{
lean::dec(x_0);
lean::dec(x_3);
return x_1;
}
}
}
obj* l___private_615858501__trim__right__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_615858501__trim__right__aux___main(x_0, x_1);
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
x_4 = l___private_615858501__trim__right__aux___main(x_1, x_3);
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
x_5 = l___private_3868098097__trim__left__aux___main(x_1, x_2);
x_6 = lean::string_iterator_to_end(x_2);
x_7 = l___private_615858501__trim__right__aux___main(x_1, x_6);
x_8 = lean::string_iterator_extract(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
x_11 = l_string_join___closed__1;
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_8, x_11);
return x_13;
}
}
obj* l___private_104996535__line__column__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; unsigned char x_13; unsigned char x_15; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_15 = lean::string_iterator_has_next(x_1);
if (x_15 == 0)
{
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
else
{
unsigned char x_23; 
lean::dec(x_2);
x_23 = 0;
x_13 = x_23;
goto lbl_14;
}
lbl_14:
{
unsigned x_24; obj* x_25; obj* x_26; obj* x_27; unsigned x_29; 
x_24 = lean::string_iterator_curr(x_1);
x_25 = lean::mk_nat_obj(10u);
x_26 = lean::mk_nat_obj(55296u);
x_27 = lean::nat_dec_lt(x_25, x_26);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_32; obj* x_33; 
lean::dec(x_27);
x_32 = lean::mk_nat_obj(57343u);
x_33 = lean::nat_dec_lt(x_32, x_25);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
unsigned x_37; 
lean::dec(x_25);
lean::dec(x_33);
x_37 = lean::unbox_uint32(x_3);
x_29 = x_37;
goto lbl_30;
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_33);
x_39 = lean::mk_nat_obj(1114112u);
x_40 = lean::nat_dec_lt(x_25, x_39);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
unsigned x_44; 
lean::dec(x_25);
lean::dec(x_40);
x_44 = lean::unbox_uint32(x_3);
x_29 = x_44;
goto lbl_30;
}
else
{
unsigned x_46; 
lean::dec(x_40);
x_46 = lean::unbox_uint32(x_25);
lean::dec(x_25);
x_29 = x_46;
goto lbl_30;
}
}
}
else
{
unsigned x_49; 
lean::dec(x_27);
x_49 = lean::unbox_uint32(x_25);
lean::dec(x_25);
x_29 = x_49;
goto lbl_30;
}
lbl_30:
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = lean::box_uint32(x_24);
x_52 = lean::box_uint32(x_29);
x_53 = lean::nat_dec_eq(x_51, x_52);
lean::dec(x_52);
lean::dec(x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; obj* x_59; obj* x_62; 
lean::dec(x_53);
lean::dec(x_3);
x_58 = lean::string_iterator_next(x_1);
x_59 = lean::nat_add(x_8, x_10);
lean::dec(x_10);
lean::dec(x_8);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_6);
lean::cnstr_set(x_62, 1, x_59);
x_0 = x_11;
x_1 = x_58;
x_2 = x_62;
goto _start;
}
else
{
obj* x_66; obj* x_67; obj* x_70; 
lean::dec(x_53);
lean::dec(x_8);
x_66 = lean::string_iterator_next(x_1);
x_67 = lean::nat_add(x_6, x_10);
lean::dec(x_10);
lean::dec(x_6);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_67);
lean::cnstr_set(x_70, 1, x_3);
x_0 = x_11;
x_1 = x_66;
x_2 = x_70;
goto _start;
}
}
}
}
else
{
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
}
}
obj* l___private_104996535__line__column__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_104996535__line__column__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_string_line__column(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_string_line__column___closed__1;
lean::inc(x_3);
x_5 = l___private_104996535__line__column__aux___main(x_1, x_2, x_3);
return x_5;
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
obj* l_char_to__string(unsigned x_0) {
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
unsigned x_1; obj* x_2; 
x_1 = lean::unbox_uint32(x_0);
x_2 = l_char_to__string(x_1);
return x_2;
}
}
obj* l___private_3344645481__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; unsigned x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_23; 
lean::dec(x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_10 = lean::string_iterator_curr(x_0);
x_11 = lean::mk_nat_obj(10u);
x_12 = lean::nat_mul(x_2, x_11);
lean::dec(x_11);
lean::dec(x_2);
x_15 = lean::box_uint32(x_10);
x_16 = lean::nat_add(x_12, x_15);
lean::dec(x_15);
lean::dec(x_12);
x_19 = lean::mk_nat_obj(48u);
x_20 = lean::mk_nat_obj(55296u);
x_21 = lean::nat_dec_lt(x_19, x_20);
lean::dec(x_20);
x_23 = lean::string_iterator_next(x_0);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_21);
x_25 = lean::mk_nat_obj(57343u);
x_26 = lean::nat_dec_lt(x_25, x_19);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_30; 
lean::dec(x_19);
lean::dec(x_26);
x_30 = lean::nat_sub(x_16, x_3);
lean::dec(x_3);
lean::dec(x_16);
x_0 = x_23;
x_1 = x_7;
x_2 = x_30;
goto _start;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_26);
x_35 = lean::mk_nat_obj(1114112u);
x_36 = lean::nat_dec_lt(x_19, x_35);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; 
lean::dec(x_19);
lean::dec(x_36);
x_40 = lean::nat_sub(x_16, x_3);
lean::dec(x_3);
lean::dec(x_16);
x_0 = x_23;
x_1 = x_7;
x_2 = x_40;
goto _start;
}
else
{
obj* x_46; 
lean::dec(x_3);
lean::dec(x_36);
x_46 = lean::nat_sub(x_16, x_19);
lean::dec(x_19);
lean::dec(x_16);
x_0 = x_23;
x_1 = x_7;
x_2 = x_46;
goto _start;
}
}
}
else
{
obj* x_52; 
lean::dec(x_3);
lean::dec(x_21);
x_52 = lean::nat_sub(x_16, x_19);
lean::dec(x_19);
lean::dec(x_16);
x_0 = x_23;
x_1 = x_7;
x_2 = x_52;
goto _start;
}
}
else
{
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
}
}
obj* l___private_3344645481__to__nat__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_3344645481__to__nat__core___main(x_0, x_1, x_2);
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
x_6 = l___private_3344645481__to__nat__core___main(x_2, x_3, x_5);
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
 l_string_has__lt = _init_l_string_has__lt();
 l_string_iterator_extract___main___closed__1 = _init_l_string_iterator_extract___main___closed__1();
 l_string_iterator_is__prefix__of__remaining = _init_l_string_iterator_is__prefix__of__remaining();
 l_string_inhabited = _init_l_string_inhabited();
 l_string_has__sizeof = _init_l_string_has__sizeof();
 l_string_has__append = _init_l_string_has__append();
 l_string_join___closed__1 = _init_l_string_join___closed__1();
 l_string_line__column___closed__1 = _init_l_string_line__column___closed__1();
}

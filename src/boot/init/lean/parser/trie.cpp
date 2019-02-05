// Lean compiler output
// Module: init.lean.parser.trie
// Imports: init.data.rbmap.default init.lean.format
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg(obj*, unsigned, obj*);
obj* l_lean_format_join__sep___main___at___private_3045062755__to__string__aux___main___spec__1(obj*, obj*);
unsigned char l_rbnode_get__color___main___rarg(obj*);
obj* l___private_4095784467__find__aux___main___rarg(obj*, obj*, obj*);
obj* l___private_4095784467__find__aux___rarg(obj*, obj*, obj*);
obj* l_lean_parser_trie_match__prefix(obj*);
obj* l___private_1312873337__match__prefix__aux(obj*);
obj* l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1(obj*);
obj* l___private_3279031763__insert__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_3045062755__to__string__aux(obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l___private_1312873337__match__prefix__aux___main(obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_char_quote__core(unsigned);
obj* l___private_3279031763__insert__aux___main(obj*);
obj* l___private_1312873337__match__prefix__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_4095784467__find__aux___main(obj*);
obj* l_lean_parser_trie_has__to__string___rarg(obj*);
obj* l_lean_parser_trie_mk(obj*);
obj* l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3(obj*);
obj* l___private_1312873337__match__prefix__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_3279031763__insert__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_to__fmt___at___private_3045062755__to__string__aux___main___spec__2(obj*);
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_trie_has__to__string(obj*);
obj* l___private_3045062755__to__string__aux___rarg(obj*);
obj* l___private_3045062755__to__string__aux___main(obj*);
obj* l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3(obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_lean_format_pretty(obj*, obj*);
obj* l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_lean_parser_trie_insert(obj*);
obj* l___private_3045062755__to__string__aux___main___rarg(obj*);
obj* l___private_3279031763__insert__aux(obj*);
obj* l_lean_parser_trie_find___rarg(obj*, obj*);
obj* l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2(obj*);
obj* l_lean_format_group___main(obj*);
obj* l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg(obj*, unsigned);
obj* l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3___rarg(obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(unsigned char, obj*);
obj* l_option_orelse___main___rarg(obj*, obj*);
obj* l_lean_parser_trie_find(obj*);
obj* l___private_4095784467__find__aux(obj*);
obj* l_lean_parser_trie_mk___closed__1;
obj* l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(obj*, unsigned, obj*);
obj* l_lean_parser_trie_mk(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_parser_trie_mk___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_lean_parser_trie_mk___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* l___private_3279031763__insert__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; unsigned x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_5);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_12 = x_2;
}
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_1, x_13);
lean::dec(x_13);
lean::dec(x_1);
x_17 = lean::string_iterator_curr(x_3);
lean::inc(x_10);
x_19 = l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg(x_10, x_17);
x_20 = l_lean_parser_trie_mk___closed__1;
lean::inc(x_20);
x_22 = l_option_get__or__else___main___rarg(x_19, x_20);
x_23 = lean::string_iterator_next(x_3);
x_24 = l___private_3279031763__insert__aux___main___rarg(x_0, x_14, x_22, x_23);
x_25 = l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg(x_10, x_17, x_24);
if (lean::is_scalar(x_12)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_12;
}
lean::cnstr_set(x_26, 0, x_8);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_2, 1);
lean::inc(x_30);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_32 = x_2;
}
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_0);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
}
}
obj* l___private_3279031763__insert__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3279031763__insert__aux___main___rarg), 4, 0);
return x_2;
}
}
obj* l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg(obj* x_0, unsigned x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::box_uint32(x_1);
x_14 = lean::nat_dec_lt(x_13, x_6);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
lean::dec(x_14);
lean::dec(x_4);
x_17 = lean::nat_dec_lt(x_6, x_13);
lean::dec(x_13);
lean::dec(x_6);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; 
lean::dec(x_17);
lean::dec(x_10);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_8);
return x_22;
}
else
{
lean::dec(x_17);
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_14);
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_13);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; obj* x_42; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 3);
lean::inc(x_38);
lean::dec(x_0);
x_41 = lean::box_uint32(x_1);
x_42 = lean::nat_dec_lt(x_41, x_34);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; 
lean::dec(x_42);
lean::dec(x_32);
x_45 = lean::nat_dec_lt(x_34, x_41);
lean::dec(x_41);
lean::dec(x_34);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; 
lean::dec(x_45);
lean::dec(x_38);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_36);
return x_50;
}
else
{
lean::dec(x_45);
lean::dec(x_36);
x_0 = x_38;
goto _start;
}
}
else
{
lean::dec(x_41);
lean::dec(x_42);
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_38);
x_0 = x_32;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(obj* x_0, unsigned x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; 
x_3 = lean::box_uint32(x_1);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_0);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_14 = x_0;
}
x_15 = lean::box_uint32(x_1);
x_16 = lean::nat_dec_lt(x_15, x_8);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; 
lean::dec(x_16);
x_18 = lean::nat_dec_lt(x_8, x_15);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_18);
if (lean::is_scalar(x_14)) {
 x_22 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_22 = x_14;
}
lean::cnstr_set(x_22, 0, x_6);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_12);
return x_22;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_15);
lean::dec(x_18);
x_25 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_12, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_14;
}
lean::cnstr_set(x_26, 0, x_6);
lean::cnstr_set(x_26, 1, x_8);
lean::cnstr_set(x_26, 2, x_10);
lean::cnstr_set(x_26, 3, x_25);
return x_26;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_15);
lean::dec(x_16);
x_29 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_6, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_8);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
x_40 = lean::box_uint32(x_1);
x_41 = lean::nat_dec_lt(x_40, x_33);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; 
lean::dec(x_41);
x_43 = lean::nat_dec_lt(x_33, x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; 
lean::dec(x_33);
lean::dec(x_35);
lean::dec(x_43);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_47 = x_39;
}
lean::cnstr_set(x_47, 0, x_31);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set(x_47, 2, x_2);
lean::cnstr_set(x_47, 3, x_37);
return x_47;
}
else
{
unsigned char x_51; 
lean::dec(x_40);
lean::dec(x_43);
lean::inc(x_37);
x_51 = l_rbnode_get__color___main___rarg(x_37);
if (x_51 == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_39);
x_53 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_37, x_1, x_2);
x_54 = l_rbnode_balance2__node___main___rarg(x_53, x_33, x_35, x_31);
return x_54;
}
else
{
obj* x_55; obj* x_56; 
x_55 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_56 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_56 = x_39;
}
lean::cnstr_set(x_56, 0, x_31);
lean::cnstr_set(x_56, 1, x_33);
lean::cnstr_set(x_56, 2, x_35);
lean::cnstr_set(x_56, 3, x_55);
return x_56;
}
}
}
else
{
unsigned char x_60; 
lean::dec(x_40);
lean::dec(x_41);
lean::inc(x_31);
x_60 = l_rbnode_get__color___main___rarg(x_31);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_39);
x_62 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_31, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_33, x_35, x_37);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_39;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_33);
lean::cnstr_set(x_65, 2, x_35);
lean::cnstr_set(x_65, 3, x_37);
return x_65;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg(obj* x_0, unsigned x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg(x_0, x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_rbnode_ins___main___at___private_3279031763__insert__aux___main___spec__3___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_rbnode_insert___at___private_3279031763__insert__aux___main___spec__2___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_3279031763__insert__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_3279031763__insert__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_3279031763__insert__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3279031763__insert__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_trie_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::string_length(x_1);
x_4 = lean::string_mk_iterator(x_1);
x_5 = l___private_3279031763__insert__aux___main___rarg(x_2, x_3, x_0, x_4);
return x_5;
}
}
obj* l_lean_parser_trie_insert(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_insert___rarg), 3, 0);
return x_2;
}
}
obj* l___private_4095784467__find__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; unsigned x_10; obj* x_11; 
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::string_iterator_curr(x_2);
x_11 = l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg(x_7, x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; 
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_2);
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_0, x_19);
lean::dec(x_19);
lean::dec(x_0);
x_23 = lean::string_iterator_next(x_2);
x_0 = x_20;
x_1 = x_16;
x_2 = x_23;
goto _start;
}
}
else
{
obj* x_28; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
return x_28;
}
}
}
obj* l___private_4095784467__find__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_4095784467__find__aux___main___rarg), 3, 0);
return x_2;
}
}
obj* l___private_4095784467__find__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_4095784467__find__aux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_4095784467__find__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_4095784467__find__aux___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_trie_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_length(x_1);
x_3 = lean::string_mk_iterator(x_1);
x_4 = l___private_4095784467__find__aux___main___rarg(x_2, x_0, x_3);
return x_4;
}
}
obj* l_lean_parser_trie_find(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_find___rarg), 2, 0);
return x_2;
}
}
obj* l___private_1312873337__match__prefix__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_16; unsigned x_17; obj* x_18; 
lean::dec(x_5);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_2);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_14, 0, x_2);
x_15 = l_option_map___rarg(x_14, x_8);
x_16 = l_option_orelse___main___rarg(x_15, x_3);
x_17 = lean::string_iterator_curr(x_2);
x_18 = l_rbnode_find___main___at___private_3279031763__insert__aux___main___spec__1___rarg(x_10, x_17);
if (lean::obj_tag(x_18) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
return x_16;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_29; 
x_22 = lean::cnstr_get(x_18, 0);
lean::inc(x_22);
lean::dec(x_18);
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_sub(x_0, x_25);
lean::dec(x_25);
lean::dec(x_0);
x_29 = lean::string_iterator_next(x_2);
x_0 = x_26;
x_1 = x_22;
x_2 = x_29;
x_3 = x_16;
goto _start;
}
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_5);
lean::dec(x_0);
x_33 = lean::cnstr_get(x_1, 0);
lean::inc(x_33);
lean::dec(x_1);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_36, 0, x_2);
x_37 = l_option_map___rarg(x_36, x_33);
x_38 = l_option_orelse___main___rarg(x_37, x_3);
return x_38;
}
}
}
obj* l___private_1312873337__match__prefix__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_1312873337__match__prefix__aux___main___rarg), 4, 0);
return x_2;
}
}
obj* l___private_1312873337__match__prefix__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_1312873337__match__prefix__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_1312873337__match__prefix__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_1312873337__match__prefix__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_trie_match__prefix___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = lean::box(0);
x_4 = l___private_1312873337__match__prefix__aux___main___rarg(x_2, x_0, x_1, x_3);
return x_4;
}
}
obj* l_lean_parser_trie_match__prefix(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_match__prefix___rarg), 2, 0);
return x_2;
}
}
obj* l___private_3045062755__to__string__aux___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3___rarg(x_1, x_4);
return x_5;
}
}
obj* l___private_3045062755__to__string__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3045062755__to__string__aux___main___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_to__fmt___at___private_3045062755__to__string__aux___main___spec__2(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_lean_format_join__sep___main___at___private_3045062755__to__string__aux___main___spec__1(obj* x_0, obj* x_1) {
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
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
if (lean::obj_tag(x_7) == 0)
{
lean::dec(x_7);
lean::dec(x_1);
return x_5;
}
else
{
unsigned char x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = 0;
lean::inc(x_1);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = l_lean_format_join__sep___main___at___private_3045062755__to__string__aux___main___spec__1(x_7, x_1);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_12);
x_18 = x_17;
return x_18;
}
}
}
}
obj* l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_0);
return x_1;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; unsigned x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3___rarg(x_3, x_1);
x_13 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_15 = l_char_quote__core(x_13);
x_16 = l_char_has__repr___closed__1;
lean::inc(x_16);
x_18 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_20 = lean::string_append(x_18, x_16);
x_21 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = l___private_3045062755__to__string__aux___main___rarg(x_7);
x_23 = lean::box(1);
x_24 = l_lean_format_join__sep___main___at___private_3045062755__to__string__aux___main___spec__1(x_22, x_23);
x_25 = lean::mk_nat_obj(2u);
x_26 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = l_lean_format_group___main(x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_21);
lean::cnstr_set(x_29, 1, x_28);
x_0 = x_9;
x_1 = x_29;
goto _start;
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; unsigned x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3___rarg(x_31, x_1);
x_41 = lean::unbox_uint32(x_33);
lean::dec(x_33);
x_43 = l_char_quote__core(x_41);
x_44 = l_char_has__repr___closed__1;
lean::inc(x_44);
x_46 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_48 = lean::string_append(x_46, x_44);
x_49 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = l___private_3045062755__to__string__aux___main___rarg(x_35);
x_51 = lean::box(1);
x_52 = l_lean_format_join__sep___main___at___private_3045062755__to__string__aux___main___spec__1(x_50, x_51);
x_53 = lean::mk_nat_obj(2u);
x_54 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_52);
x_55 = l_lean_format_group___main(x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_40);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_49);
lean::cnstr_set(x_57, 1, x_56);
x_0 = x_37;
x_1 = x_57;
goto _start;
}
}
}
}
obj* l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___at___private_3045062755__to__string__aux___main___spec__3___rarg), 2, 0);
return x_2;
}
}
obj* l___private_3045062755__to__string__aux___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_3045062755__to__string__aux___main___rarg(x_0);
return x_1;
}
}
obj* l___private_3045062755__to__string__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3045062755__to__string__aux___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_trie_has__to__string___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l___private_3045062755__to__string__aux___main___rarg(x_0);
x_2 = lean::box(1);
x_3 = l_lean_format_join__sep___main___at___private_3045062755__to__string__aux___main___spec__1(x_1, x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_lean_format_pretty(x_3, x_4);
return x_5;
}
}
obj* l_lean_parser_trie_has__to__string(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_has__to__string___rarg), 1, 0);
return x_2;
}
}
void initialize_init_data_rbmap_default();
void initialize_init_lean_format();
static bool _G_initialized = false;
void initialize_init_lean_parser_trie() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_rbmap_default();
 initialize_init_lean_format();
 l_lean_parser_trie_mk___closed__1 = _init_l_lean_parser_trie_mk___closed__1();
}

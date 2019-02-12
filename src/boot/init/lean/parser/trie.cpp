// Lean compiler output
// Module: init.lean.parser.trie
// Imports: init.data.rbmap.default init.lean.format
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
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_lean_parser_trie_has__to__string(obj*);
obj* l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___main(obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux(obj*);
obj* l_lean_parser_trie_mk(obj*);
obj* l_lean_parser_trie_find___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___main(obj*);
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(obj*, uint32);
obj* l_lean_parser_trie_match__prefix(obj*);
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux(obj*);
obj* l_option_orelse___main___rarg(obj*, obj*);
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___rarg(obj*, obj*, obj*);
obj* l_lean_parser_trie_mk___closed__1;
obj* l___private_init_lean_parser_trie_1__insert__aux___main___rarg(obj*, obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_trie_find(obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___rarg(obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___main(obj*);
obj* l_lean_format_group___main(obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(obj*);
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2(obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux(obj*);
obj* l_lean_format_pretty(obj*, obj*);
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(obj*, uint32, obj*);
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1(obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2(obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main(obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(obj*, uint32, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3(obj*);
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l_lean_parser_trie_insert(obj*);
obj* l_lean_parser_trie_has__to__string___rarg(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___main___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__find__aux(obj*);
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
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_13; uint8 x_14; 
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
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_4);
x_16 = lean::nat_dec_lt(x_6, x_13);
lean::dec(x_13);
lean::dec(x_6);
if (x_16 == 0)
{
obj* x_20; 
lean::dec(x_10);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_8);
return x_20;
}
else
{
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_10);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_37; uint8 x_38; 
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 2);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 3);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::box_uint32(x_1);
x_38 = lean::nat_dec_lt(x_37, x_30);
if (x_38 == 0)
{
uint8 x_40; 
lean::dec(x_28);
x_40 = lean::nat_dec_lt(x_30, x_37);
lean::dec(x_37);
lean::dec(x_30);
if (x_40 == 0)
{
obj* x_44; 
lean::dec(x_34);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_32);
return x_44;
}
else
{
lean::dec(x_32);
x_0 = x_34;
goto _start;
}
}
else
{
lean::dec(x_30);
lean::dec(x_37);
lean::dec(x_32);
lean::dec(x_34);
x_0 = x_28;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; uint8 x_16; 
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
if (x_16 == 0)
{
uint8 x_17; 
x_17 = lean::nat_dec_lt(x_8, x_15);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_10);
lean::dec(x_8);
if (lean::is_scalar(x_14)) {
 x_20 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_20 = x_14;
}
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_15);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_12);
return x_20;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_15);
x_22 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_12, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_23 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_23 = x_14;
}
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_8);
lean::cnstr_set(x_23, 2, x_10);
lean::cnstr_set(x_23, 3, x_22);
return x_23;
}
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_15);
x_25 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_6, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_14;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_8);
lean::cnstr_set(x_26, 2, x_10);
lean::cnstr_set(x_26, 3, x_12);
return x_26;
}
}
default:
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; uint8 x_37; 
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 2);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 3);
lean::inc(x_33);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_35 = x_0;
}
x_36 = lean::box_uint32(x_1);
x_37 = lean::nat_dec_lt(x_36, x_29);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = lean::nat_dec_lt(x_29, x_36);
if (x_38 == 0)
{
obj* x_41; 
lean::dec(x_29);
lean::dec(x_31);
if (lean::is_scalar(x_35)) {
 x_41 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_41 = x_35;
}
lean::cnstr_set(x_41, 0, x_27);
lean::cnstr_set(x_41, 1, x_36);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_33);
return x_41;
}
else
{
uint8 x_44; 
lean::dec(x_36);
lean::inc(x_33);
x_44 = l_rbnode_get__color___main___rarg(x_33);
if (x_44 == 0)
{
obj* x_46; obj* x_47; 
lean::dec(x_35);
x_46 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_33, x_1, x_2);
x_47 = l_rbnode_balance2__node___main___rarg(x_46, x_29, x_31, x_27);
return x_47;
}
else
{
obj* x_48; obj* x_49; 
x_48 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_33, x_1, x_2);
if (lean::is_scalar(x_35)) {
 x_49 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_49 = x_35;
}
lean::cnstr_set(x_49, 0, x_27);
lean::cnstr_set(x_49, 1, x_29);
lean::cnstr_set(x_49, 2, x_31);
lean::cnstr_set(x_49, 3, x_48);
return x_49;
}
}
}
else
{
uint8 x_52; 
lean::dec(x_36);
lean::inc(x_27);
x_52 = l_rbnode_get__color___main___rarg(x_27);
if (x_52 == 0)
{
obj* x_54; obj* x_55; 
lean::dec(x_35);
x_54 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_27, x_1, x_2);
x_55 = l_rbnode_balance1__node___main___rarg(x_54, x_29, x_31, x_33);
return x_55;
}
else
{
obj* x_56; obj* x_57; 
x_56 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_27, x_1, x_2);
if (lean::is_scalar(x_35)) {
 x_57 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_57 = x_35;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_29);
lean::cnstr_set(x_57, 2, x_31);
lean::cnstr_set(x_57, 3, x_33);
return x_57;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; uint32 x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_11 = x_2;
}
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_1, x_12);
lean::dec(x_12);
lean::dec(x_1);
x_16 = lean::string_iterator_curr(x_3);
lean::inc(x_9);
x_18 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_9, x_16);
x_19 = l_lean_parser_trie_mk___closed__1;
lean::inc(x_19);
x_21 = l_option_get__or__else___main___rarg(x_18, x_19);
x_22 = lean::string_iterator_next(x_3);
x_23 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_0, x_13, x_21, x_22);
x_24 = l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(x_9, x_16, x_23);
if (lean::is_scalar(x_11)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_11;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
lean::dec(x_3);
x_28 = lean::cnstr_get(x_2, 1);
lean::inc(x_28);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_30 = x_2;
}
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_0);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insert__aux___main___rarg), 4, 0);
return x_2;
}
}
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_0, x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insert__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_trie_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::string_length(x_1);
x_4 = lean::string_mk_iterator(x_1);
x_5 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_2, x_3, x_0, x_4);
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
obj* l___private_init_lean_parser_trie_2__find__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; uint32 x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_6, x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_22; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_sub(x_0, x_18);
lean::dec(x_18);
lean::dec(x_0);
x_22 = lean::string_iterator_next(x_2);
x_0 = x_19;
x_1 = x_15;
x_2 = x_22;
goto _start;
}
}
else
{
obj* x_26; 
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
lean::dec(x_1);
return x_26;
}
}
}
obj* l___private_init_lean_parser_trie_2__find__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__find__aux___main___rarg), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_2__find__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_2__find__aux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_2__find__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__find__aux___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_trie_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_length(x_1);
x_3 = lean::string_mk_iterator(x_1);
x_4 = l___private_init_lean_parser_trie_2__find__aux___main___rarg(x_2, x_0, x_3);
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
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_15; uint32 x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_2);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_2);
x_14 = l_option_map___rarg(x_13, x_7);
x_15 = l_option_orelse___main___rarg(x_14, x_3);
x_16 = lean::string_iterator_curr(x_2);
x_17 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_9, x_16);
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_2);
return x_15;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_28; 
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
lean::dec(x_17);
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_sub(x_0, x_24);
lean::dec(x_24);
lean::dec(x_0);
x_28 = lean::string_iterator_next(x_2);
x_0 = x_25;
x_1 = x_21;
x_2 = x_28;
x_3 = x_15;
goto _start;
}
}
else
{
obj* x_31; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
lean::dec(x_1);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_34, 0, x_2);
x_35 = l_option_map___rarg(x_34, x_31);
x_36 = l_option_orelse___main___rarg(x_35, x_3);
return x_36;
}
}
}
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_3__match__prefix__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__match__prefix__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_trie_match__prefix___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = lean::box(0);
x_4 = l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg(x_2, x_0, x_1, x_3);
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
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2(obj* x_0) {
_start:
{
return x_0;
}
}
obj* l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(obj* x_0, obj* x_1) {
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
uint8 x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = 0;
lean::inc(x_1);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_7, x_1);
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
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(obj* x_0, obj* x_1) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint32 x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_3, x_1);
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
x_22 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_7);
x_23 = lean::box(1);
x_24 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_22, x_23);
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
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_40; uint32 x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_31, x_1);
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
x_50 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_35);
x_51 = lean::box(1);
x_52 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_50, x_51);
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
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
x_5 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_1, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__to__string__aux___main___rarg), 1, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__to__string__aux___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_trie_has__to__string___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_0);
x_2 = lean::box(1);
x_3 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_1, x_2);
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

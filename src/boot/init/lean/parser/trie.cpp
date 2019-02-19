// Lean compiler output
// Module: init.lean.parser.trie
// Imports: init.data.rbmap.default init.lean.format
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
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l___private_init_lean_parser_trie_4__to__string__aux(obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_option_orelse___main___rarg(obj*, obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___rarg(obj*, obj*, obj*);
obj* l_lean_parser_trie_mk___closed__1;
obj* l___private_init_lean_parser_trie_1__insert__aux___main___rarg(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
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
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2(obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
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
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* l_lean_parser_trie_mk(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_parser_trie_mk___closed__1;
return x_2;
}
}
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint32 x_12; uint8 x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_14 = x_1 < x_12;
if (x_14 == 0)
{
uint8 x_16; 
lean::dec(x_3);
x_16 = x_12 < x_1;
if (x_16 == 0)
{
obj* x_18; 
lean::dec(x_9);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_7);
return x_18;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
x_0 = x_3;
goto _start;
}
}
default:
{
obj* x_24; obj* x_26; obj* x_28; obj* x_30; uint32 x_33; uint8 x_35; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 2);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 3);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_35 = x_1 < x_33;
if (x_35 == 0)
{
uint8 x_37; 
lean::dec(x_24);
x_37 = x_33 < x_1;
if (x_37 == 0)
{
obj* x_39; 
lean::dec(x_30);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_28);
return x_39;
}
else
{
lean::dec(x_28);
x_0 = x_30;
goto _start;
}
}
else
{
lean::dec(x_28);
lean::dec(x_30);
x_0 = x_24;
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
obj* x_3; obj* x_4; 
x_3 = lean::box_uint32(x_1);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; uint8 x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
} else {
 lean::dec(x_0);
 x_13 = lean::box(0);
}
x_14 = lean::unbox_uint32(x_7);
x_15 = x_1 < x_14;
if (x_15 == 0)
{
uint8 x_16; 
x_16 = x_14 < x_1;
if (x_16 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_7);
lean::dec(x_9);
x_19 = lean::box_uint32(x_1);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_11);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_22 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_22 = x_13;
}
lean::cnstr_set(x_22, 0, x_5);
lean::cnstr_set(x_22, 1, x_7);
lean::cnstr_set(x_22, 2, x_9);
lean::cnstr_set(x_22, 3, x_21);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_24 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_24 = x_13;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_7);
lean::cnstr_set(x_24, 2, x_9);
lean::cnstr_set(x_24, 3, x_11);
return x_24;
}
}
default:
{
obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_33; uint32 x_34; uint8 x_35; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 2);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 3);
lean::inc(x_31);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_33 = x_0;
} else {
 lean::dec(x_0);
 x_33 = lean::box(0);
}
x_34 = lean::unbox_uint32(x_27);
x_35 = x_1 < x_34;
if (x_35 == 0)
{
uint8 x_36; 
x_36 = x_34 < x_1;
if (x_36 == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_29);
lean::dec(x_27);
x_39 = lean::box_uint32(x_1);
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_25);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set(x_40, 2, x_2);
lean::cnstr_set(x_40, 3, x_31);
return x_40;
}
else
{
uint8 x_42; 
lean::inc(x_31);
x_42 = l_rbnode_get__color___main___rarg(x_31);
if (x_42 == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_33);
x_44 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_31, x_1, x_2);
x_45 = l_rbnode_balance2__node___main___rarg(x_44, x_27, x_29, x_25);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
x_46 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_31, x_1, x_2);
if (lean::is_scalar(x_33)) {
 x_47 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_47 = x_33;
}
lean::cnstr_set(x_47, 0, x_25);
lean::cnstr_set(x_47, 1, x_27);
lean::cnstr_set(x_47, 2, x_29);
lean::cnstr_set(x_47, 3, x_46);
return x_47;
}
}
}
else
{
uint8 x_49; 
lean::inc(x_25);
x_49 = l_rbnode_get__color___main___rarg(x_25);
if (x_49 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_33);
x_51 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_25, x_1, x_2);
x_52 = l_rbnode_balance1__node___main___rarg(x_51, x_27, x_29, x_31);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_25, x_1, x_2);
if (lean::is_scalar(x_33)) {
 x_54 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_54 = x_33;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_27);
lean::cnstr_set(x_54, 2, x_29);
lean::cnstr_set(x_54, 3, x_31);
return x_54;
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
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; uint32 x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
} else {
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_1, x_11);
lean::dec(x_1);
x_14 = lean::string_iterator_curr(x_3);
lean::inc(x_8);
x_16 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_8, x_14);
x_17 = l_lean_parser_trie_mk___closed__1;
x_18 = l_option_get__or__else___main___rarg(x_16, x_17);
x_19 = lean::string_iterator_next(x_3);
x_20 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_0, x_12, x_18, x_19);
x_21 = l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(x_8, x_14, x_20);
if (lean::is_scalar(x_10)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_10;
}
lean::cnstr_set(x_22, 0, x_6);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_3);
x_25 = lean::cnstr_get(x_2, 1);
lean::inc(x_25);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_27 = x_2;
} else {
 lean::dec(x_2);
 x_27 = lean::box(0);
}
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_0);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_25);
return x_29;
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
if (x_4 == 0)
{
obj* x_5; uint32 x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_5, x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; 
lean::dec(x_0);
lean::dec(x_2);
x_12 = lean::box(0);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; obj* x_19; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_0, x_16);
lean::dec(x_0);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_17;
x_1 = x_13;
x_2 = x_19;
goto _start;
}
}
else
{
obj* x_23; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
return x_23;
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
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_12, 0, x_2);
x_13 = l_option_map___rarg(x_12, x_6);
x_14 = l_option_orelse___main___rarg(x_13, x_3);
x_15 = lean::string_iterator_curr(x_2);
x_16 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_8, x_15);
if (lean::obj_tag(x_16) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_14;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_sub(x_0, x_22);
lean::dec(x_0);
x_25 = lean::string_iterator_next(x_2);
x_0 = x_23;
x_1 = x_19;
x_2 = x_25;
x_3 = x_14;
goto _start;
}
}
else
{
obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_0);
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_31, 0, x_2);
x_32 = l_option_map___rarg(x_31, x_28);
x_33 = l_option_orelse___main___rarg(x_32, x_3);
return x_33;
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
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_1);
return x_4;
}
else
{
uint8 x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = 0;
lean::inc(x_1);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_10);
x_13 = x_12;
x_14 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_6, x_1);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_10);
x_16 = x_15;
return x_16;
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
return x_1;
}
default:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; uint32 x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_2, x_1);
x_12 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_14 = l_char_quote__core(x_12);
x_15 = l_char_has__repr___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = lean::string_append(x_16, x_15);
x_19 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_6);
x_21 = lean::box(1);
x_22 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_20, x_21);
x_23 = lean::mk_nat_obj(2u);
x_24 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = l_lean_format_group___main(x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_19);
lean::cnstr_set(x_27, 1, x_26);
x_0 = x_8;
x_1 = x_27;
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
lean::mark_persistent(l_lean_parser_trie_mk___closed__1);
}

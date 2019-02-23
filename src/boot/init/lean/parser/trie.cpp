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
obj* l_lean_parser_trie_insert___boxed(obj*);
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_trie_has__to__string(obj*);
obj* l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4(obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___main(obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___boxed(obj*);
obj* l_lean_parser_trie_has__to__string___rarg___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux(obj*);
obj* l_lean_parser_trie_mk(obj*);
obj* l_lean_parser_trie_find___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___main(obj*);
obj* l_lean_parser_trie_match__prefix___boxed(obj*);
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(obj*, uint32);
obj* l_lean_parser_trie_find___boxed(obj*);
obj* l_lean_parser_trie_match__prefix(obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___rarg___boxed(obj*);
obj* l_list_zip___rarg___lambda__1(obj*, obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l___private_init_lean_parser_trie_4__to__string__aux(obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___main___rarg___boxed(obj*, obj*, obj*, obj*);
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
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___boxed(obj*);
obj* l_lean_parser_trie_mk___closed__1;
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___main___rarg(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
extern obj* l_char_has__repr___closed__1;
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___main___boxed(obj*);
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_trie_find(obj*);
obj* l_lean_parser_trie_has__to__string___boxed(obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___rarg___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___rarg(obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___main(obj*);
obj* l_lean_format_group___main(obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(obj*);
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2(obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux(obj*);
obj* l_lean_format_pretty(obj*, obj*);
obj* l___private_init_lean_parser_trie_4__to__string__aux___boxed(obj*);
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(obj*, uint32, obj*);
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1(obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___boxed(obj*);
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_1__insert__aux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___boxed(obj*);
obj* l_lean_parser_trie_mk___boxed(obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___boxed(obj*);
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2(obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main(obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(obj*, uint32, obj*);
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg___boxed(obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3(obj*);
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___boxed(obj*);
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l_lean_parser_trie_insert(obj*);
obj* l_lean_parser_trie_has__to__string___rarg(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux___main___rarg(obj*, obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__find__aux(obj*);
obj* _init_l_lean_parser_trie_mk___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_trie_mk(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_mk___closed__1;
return x_1;
}
}
obj* l_lean_parser_trie_mk___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_mk(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint32 x_12; uint8 x_13; 
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
x_13 = x_1 < x_12;
if (x_13 == 0)
{
uint8 x_15; 
lean::dec(x_3);
x_15 = x_12 < x_1;
if (x_15 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
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
lean::dec(x_7);
lean::dec(x_9);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = 0;
x_4 = lean::box_uint32(x_1);
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_0);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_3);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint32 x_17; uint8 x_18; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
x_12 = lean::cnstr_get(x_0, 2);
x_14 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_16 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
x_17 = lean::unbox_uint32(x_10);
x_18 = x_1 < x_17;
if (x_18 == 0)
{
uint8 x_19; 
x_19 = x_17 < x_1;
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_12);
x_21 = lean::box_uint32(x_1);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_16;
}
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_14);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_7);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_14, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_16;
}
lean::cnstr_set(x_25, 0, x_8);
lean::cnstr_set(x_25, 1, x_10);
lean::cnstr_set(x_25, 2, x_12);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_7);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_8, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_10);
lean::cnstr_set(x_28, 2, x_12);
lean::cnstr_set(x_28, 3, x_14);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_7);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; uint32 x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = lean::unbox_uint32(x_32);
x_40 = x_1 < x_39;
if (x_40 == 0)
{
uint8 x_41; 
x_41 = x_39 < x_1;
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_34);
x_43 = lean::box_uint32(x_1);
if (lean::is_scalar(x_38)) {
 x_44 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_44 = x_38;
}
lean::cnstr_set(x_44, 0, x_30);
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set(x_44, 2, x_2);
lean::cnstr_set(x_44, 3, x_36);
lean::cnstr_set_scalar(x_44, sizeof(void*)*4, x_7);
x_45 = x_44;
return x_45;
}
else
{
uint8 x_46; 
x_46 = l_rbnode_is__red___main___rarg(x_36);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_38;
}
lean::cnstr_set(x_48, 0, x_30);
lean::cnstr_set(x_48, 1, x_32);
lean::cnstr_set(x_48, 2, x_34);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_7);
x_49 = x_48;
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_32);
lean::cnstr_set(x_51, 2, x_34);
lean::cnstr_set(x_51, 3, x_50);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_7);
x_52 = x_51;
x_53 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_36, x_1, x_2);
x_54 = l_rbnode_balance2___main___rarg(x_52, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
x_55 = l_rbnode_is__red___main___rarg(x_30);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_38;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_32);
lean::cnstr_set(x_57, 2, x_34);
lean::cnstr_set(x_57, 3, x_36);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_7);
x_58 = x_57;
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_60 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_60 = x_38;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_32);
lean::cnstr_set(x_60, 2, x_34);
lean::cnstr_set(x_60, 3, x_36);
lean::cnstr_set_scalar(x_60, sizeof(void*)*4, x_7);
x_61 = x_60;
x_62 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_30, x_1, x_2);
x_63 = l_rbnode_balance1___main___rarg(x_61, x_62);
return x_63;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = 0;
x_4 = lean::box_uint32(x_1);
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_4);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_0);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_3);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint32 x_17; uint8 x_18; 
x_8 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_0, 1);
x_12 = lean::cnstr_get(x_0, 2);
x_14 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_16 = x_0;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
x_17 = lean::unbox_uint32(x_10);
x_18 = x_1 < x_17;
if (x_18 == 0)
{
uint8 x_19; 
x_19 = x_17 < x_1;
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_12);
x_21 = lean::box_uint32(x_1);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_16;
}
lean::cnstr_set(x_22, 0, x_8);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_14);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_7);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_14, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_16;
}
lean::cnstr_set(x_25, 0, x_8);
lean::cnstr_set(x_25, 1, x_10);
lean::cnstr_set(x_25, 2, x_12);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_7);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_8, x_1, x_2);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_10);
lean::cnstr_set(x_28, 2, x_12);
lean::cnstr_set(x_28, 3, x_14);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_7);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; uint32 x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = lean::unbox_uint32(x_32);
x_40 = x_1 < x_39;
if (x_40 == 0)
{
uint8 x_41; 
x_41 = x_39 < x_1;
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_34);
x_43 = lean::box_uint32(x_1);
if (lean::is_scalar(x_38)) {
 x_44 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_44 = x_38;
}
lean::cnstr_set(x_44, 0, x_30);
lean::cnstr_set(x_44, 1, x_43);
lean::cnstr_set(x_44, 2, x_2);
lean::cnstr_set(x_44, 3, x_36);
lean::cnstr_set_scalar(x_44, sizeof(void*)*4, x_7);
x_45 = x_44;
return x_45;
}
else
{
uint8 x_46; 
x_46 = l_rbnode_is__red___main___rarg(x_36);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_38;
}
lean::cnstr_set(x_48, 0, x_30);
lean::cnstr_set(x_48, 1, x_32);
lean::cnstr_set(x_48, 2, x_34);
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_7);
x_49 = x_48;
return x_49;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_32);
lean::cnstr_set(x_51, 2, x_34);
lean::cnstr_set(x_51, 3, x_50);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_7);
x_52 = x_51;
x_53 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_36, x_1, x_2);
x_54 = l_rbnode_balance2___main___rarg(x_52, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
x_55 = l_rbnode_is__red___main___rarg(x_30);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_57 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_57 = x_38;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_32);
lean::cnstr_set(x_57, 2, x_34);
lean::cnstr_set(x_57, 3, x_36);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_7);
x_58 = x_57;
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_59 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_60 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_60 = x_38;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_32);
lean::cnstr_set(x_60, 2, x_34);
lean::cnstr_set(x_60, 3, x_36);
lean::cnstr_set_scalar(x_60, sizeof(void*)*4, x_7);
x_61 = x_60;
x_62 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_30, x_1, x_2);
x_63 = l_rbnode_balance1___main___rarg(x_61, x_62);
return x_63;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg___boxed), 3, 0);
return x_1;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; uint32 x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
x_6 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_10 = x_2;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_1, x_11);
x_13 = lean::string_iterator_curr(x_3);
lean::inc(x_8);
x_15 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_8, x_13);
x_16 = l_lean_parser_trie_mk___closed__1;
x_17 = l_option_get__or__else___main___rarg(x_15, x_16);
lean::dec(x_15);
x_19 = lean::string_iterator_next(x_3);
x_20 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_0, x_12, x_17, x_19);
lean::dec(x_12);
x_22 = l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___rarg(x_8, x_13, x_20);
if (lean::is_scalar(x_10)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_10;
}
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_3);
x_25 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_27 = x_2;
} else {
 lean::inc(x_25);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insert__aux___main___rarg___boxed), 4, 0);
return x_1;
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
obj* l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__4(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_insert___at___private_init_lean_parser_trie_1__insert__aux___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_1__insert__aux___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insert__aux___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_1__insert__aux___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_1__insert__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_1__insert__aux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_trie_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::string_length(x_1);
x_4 = lean::string_mk_iterator(x_1);
x_5 = l___private_init_lean_parser_trie_1__insert__aux___main___rarg(x_2, x_3, x_0, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_parser_trie_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_insert___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_trie_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_insert(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__find__aux___main___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_2__find__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_2__find__aux___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__find__aux___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_2__find__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_2__find__aux(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_find___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_trie_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_find(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_14; uint32 x_17; obj* x_18; 
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
lean::dec(x_3);
lean::dec(x_13);
x_17 = lean::string_iterator_curr(x_2);
x_18 = l_rbnode_find___main___at___private_init_lean_parser_trie_1__insert__aux___main___spec__1___rarg(x_8, x_17);
if (lean::obj_tag(x_18) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_14;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_sub(x_0, x_24);
lean::dec(x_0);
x_27 = lean::string_iterator_next(x_2);
x_0 = x_25;
x_1 = x_21;
x_2 = x_27;
x_3 = x_14;
goto _start;
}
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_list_zip___rarg___lambda__1), 2, 1);
lean::closure_set(x_33, 0, x_2);
x_34 = l_option_map___rarg(x_33, x_30);
x_35 = l_option_orelse___main___rarg(x_34, x_3);
lean::dec(x_3);
lean::dec(x_34);
return x_35;
}
}
}
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__match__prefix__aux___main___rarg), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_3__match__prefix__aux___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__match__prefix__aux___rarg), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_3__match__prefix__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_3__match__prefix__aux(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_match__prefix___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_trie_match__prefix___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_match__prefix(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2(obj* x_0) {
_start:
{
lean::inc(x_0);
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
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
return x_7;
}
else
{
obj* x_10; uint8 x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = 0;
lean::inc(x_1);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_1);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_13);
x_16 = x_15;
x_17 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_4, x_1);
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_13);
x_19 = x_18;
return x_19;
}
}
}
}
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint32 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::cnstr_get(x_0, 3);
x_6 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_2, x_1);
x_7 = lean::unbox_uint32(x_3);
x_8 = l_char_quote__core(x_7);
x_9 = l_char_has__repr___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = lean::string_append(x_10, x_9);
x_13 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_4);
x_15 = lean::box(1);
x_16 = l_lean_format_join__sep___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__1(x_14, x_15);
x_17 = lean::mk_nat_obj(2u);
x_18 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = l_lean_format_group___main(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_6);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
x_0 = x_5;
x_1 = x_21;
goto _start;
}
}
}
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::box(0);
x_3 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__to__string__aux___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_to__fmt___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_fold___main___at___private_init_lean_parser_trie_4__to__string__aux___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_4__to__string__aux___main___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_4__to__string__aux___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__to__string__aux___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_4__to__string__aux___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__to__string__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_4__to__string__aux(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_trie_has__to__string___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_trie_has__to__string___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_has__to__string___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_trie_has__to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_trie_has__to__string(x_0);
lean::dec(x_0);
return x_1;
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

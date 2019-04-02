// Lean compiler output
// Module: init.lean.parser.trie
// Imports: init.data.rbmap.default init.lean.format init.lean.parser.parsec
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
obj* l_Lean_Parser_Trie_HasToString___boxed(obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___boxed(obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix___rarg(obj*, obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_insert___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_Inhabited___boxed(obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_HasToString___rarg___boxed(obj*);
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___boxed(obj*);
obj* l_Lean_Parser_Trie_find(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___boxed(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1(obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4(obj*);
extern obj* l_Lean_Options_empty;
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(obj*, uint32, obj*);
obj* l_Lean_Parser_Trie_empty___boxed(obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___boxed(obj*);
obj* l_Lean_Parser_Trie_insert___rarg(obj*, obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_Lean_Parser_Trie_Inhabited(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___boxed(obj*);
obj* l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___boxed(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg(obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Trie_find___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj*, obj*, obj*);
obj* l_String_OldIterator_next___main(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__findAux(obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3(obj*);
obj* l_Lean_Parser_Trie_HasToString___rarg(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main___boxed(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l___private_init_lean_parser_trie_2__insertAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main(obj*);
obj* l_Char_quoteCore(uint32);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_empty(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_7__toStringAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg(obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___boxed(obj*);
obj* l_Lean_Parser_Trie_find___rarg___boxed(obj*, obj*);
obj* l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___boxed(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_HasToString(obj*);
obj* l_Lean_Parser_Trie_insert___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg___boxed(obj*);
obj* l_Lean_Parser_Trie_matchPrefix(obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux(obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3(obj*);
obj* l_Lean_Parser_Trie_empty___closed__1;
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(obj*, uint32, obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(obj*, uint32, obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_RBNode_balance1___main___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___boxed(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(obj*, uint32, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___boxed(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___boxed(obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___boxed(obj*);
obj* l_Lean_Parser_Trie_insert(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___boxed(obj*);
obj* _init_l_Lean_Parser_Trie_empty___closed__1() {
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
obj* l_Lean_Parser_Trie_empty(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_empty___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_Trie_empty___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_empty(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_Inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_empty___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_Trie_Inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_Inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_utf8_at_end(x_0, x_2);
if (x_3 == 0)
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::string_utf8_get(x_0, x_2);
x_5 = lean::string_utf8_next(x_0, x_2);
x_6 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_0, x_1, x_5);
lean::dec(x_5);
x_8 = lean::box(0);
x_9 = lean::box_uint32(x_4);
x_10 = l_RBNode_singleton___rarg(x_9, x_6);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_1);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_1__insertEmptyAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_1__insertEmptyAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
x_24 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_14, x_1, x_2);
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
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_8, x_1, x_2);
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
x_46 = l_RBNode_isRed___main___rarg(x_36);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_36, x_1, x_2);
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
x_53 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_36, x_1, x_2);
x_54 = l_RBNode_balance2___main___rarg(x_52, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
x_55 = l_RBNode_isRed___main___rarg(x_30);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_30, x_1, x_2);
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
x_62 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_30, x_1, x_2);
x_63 = l_RBNode_balance1___main___rarg(x_61, x_62);
return x_63;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
x_24 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_14, x_1, x_2);
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
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_8, x_1, x_2);
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
x_46 = l_RBNode_isRed___main___rarg(x_36);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_36, x_1, x_2);
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
x_53 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_36, x_1, x_2);
x_54 = l_RBNode_balance2___main___rarg(x_52, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
x_55 = l_RBNode_isRed___main___rarg(x_30);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_30, x_1, x_2);
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
x_62 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_30, x_1, x_2);
x_63 = l_RBNode_balance1___main___rarg(x_61, x_62);
return x_63;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
x_24 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_14, x_1, x_2);
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
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_8, x_1, x_2);
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
x_46 = l_RBNode_isRed___main___rarg(x_36);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_36, x_1, x_2);
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
x_53 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_36, x_1, x_2);
x_54 = l_RBNode_balance2___main___rarg(x_52, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
x_55 = l_RBNode_isRed___main___rarg(x_30);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_30, x_1, x_2);
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
x_62 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_30, x_1, x_2);
x_63 = l_RBNode_balance1___main___rarg(x_61, x_62);
return x_63;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
x_24 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_14, x_1, x_2);
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
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_8, x_1, x_2);
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
x_46 = l_RBNode_isRed___main___rarg(x_36);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_36, x_1, x_2);
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
x_53 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_36, x_1, x_2);
x_54 = l_RBNode_balance2___main___rarg(x_52, x_53);
return x_54;
}
}
}
else
{
uint8 x_55; 
x_55 = l_RBNode_isRed___main___rarg(x_30);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_30, x_1, x_2);
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
x_62 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_30, x_1, x_2);
x_63 = l_RBNode_balance1___main___rarg(x_61, x_62);
return x_63;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(obj* x_0, uint32 x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_8 = x_2;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::string_utf8_at_end(x_0, x_3);
if (x_9 == 0)
{
uint32 x_10; obj* x_11; obj* x_13; 
x_10 = lean::string_utf8_get(x_0, x_3);
x_11 = lean::string_utf8_next(x_0, x_3);
lean::inc(x_6);
x_13 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_6, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_0, x_1, x_11);
lean::dec(x_11);
x_16 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_6, x_10, x_14);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_8;
}
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
lean::dec(x_13);
x_21 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_0, x_1, x_18, x_11);
lean::dec(x_11);
x_23 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_6, x_10, x_21);
if (lean::is_scalar(x_8)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_8;
}
lean::cnstr_set(x_24, 0, x_4);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_4);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_1);
if (lean::is_scalar(x_8)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_8;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_6);
return x_27;
}
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_0, x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_2__insertAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__insertAux___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_2__insertAux___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_2__insertAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_2, x_0, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Trie_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_insert___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_insert___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Trie_insert___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Trie_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_insert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; uint8 x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::string_utf8_at_end(x_0, x_2);
if (x_8 == 0)
{
uint32 x_10; obj* x_11; 
lean::dec(x_3);
x_10 = lean::string_utf8_get(x_0, x_2);
x_11 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_5, x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; 
lean::dec(x_2);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_1 = x_14;
x_2 = x_17;
goto _start;
}
}
else
{
lean::dec(x_5);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_3__findAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_3__findAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__findAux___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_3__findAux___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_3__findAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_1, x_0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Trie_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_find___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_find___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Trie_find___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Trie_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_find(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_4 = x_2;
} else {
 lean::dec(x_2);
 x_4 = lean::box(0);
}
if (lean::is_scalar(x_4)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_4;
}
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_0);
return x_5;
}
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__updtAcc___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_4__updtAcc(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::string_utf8_at_end(x_0, x_2);
if (x_9 == 0)
{
obj* x_11; uint32 x_12; obj* x_13; 
lean::inc(x_2);
x_11 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_4, x_2, x_3);
x_12 = lean::string_utf8_get(x_0, x_2);
x_13 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_6, x_12);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_2);
return x_11;
}
else
{
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_1 = x_15;
x_2 = x_18;
x_3 = x_11;
goto _start;
}
}
else
{
obj* x_22; 
lean::dec(x_6);
x_22 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_4, x_2, x_3);
return x_22;
}
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_5__matchPrefixAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_5__matchPrefixAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
x_6 = l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(x_0, x_1, x_2, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Trie_matchPrefix(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_matchPrefix___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Trie_matchPrefix___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_Trie_matchPrefix___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_matchPrefix(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = lean::nat_dec_eq(x_0, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; uint32 x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = l_String_OldIterator_curr___main(x_2);
x_15 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_8, x_14);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_15) == 0)
{
lean::dec(x_12);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_18;
x_2 = x_21;
goto _start;
}
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_3);
x_24 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_26 = x_6;
} else {
 lean::inc(x_24);
 lean::dec(x_6);
 x_26 = lean::box(0);
}
lean::inc(x_2);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_2);
lean::cnstr_set(x_28, 1, x_24);
if (lean::is_scalar(x_26)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_26;
}
lean::cnstr_set(x_29, 0, x_28);
if (lean::obj_tag(x_15) == 0)
{
lean::dec(x_12);
lean::dec(x_2);
return x_29;
}
else
{
obj* x_32; obj* x_35; 
x_32 = lean::cnstr_get(x_15, 0);
lean::inc(x_32);
lean::dec(x_15);
x_35 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_32;
x_2 = x_35;
x_3 = x_29;
goto _start;
}
}
}
else
{
obj* x_38; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_1, 0);
lean::inc(x_38);
lean::dec(x_1);
if (lean::obj_tag(x_38) == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_3);
x_43 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_45 = x_38;
} else {
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_2);
lean::cnstr_set(x_46, 1, x_43);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_6__oldMatchPrefixAux___rarg), 4, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_6__oldMatchPrefixAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_oldMatchPrefix___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_String_OldIterator_remaining___main(x_1);
x_3 = lean::box(0);
x_4 = l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg(x_2, x_0, x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Trie_oldMatchPrefix(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_oldMatchPrefix___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_oldMatchPrefix___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_oldMatchPrefix(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(obj* x_0, obj* x_1) {
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
x_17 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(x_4, x_1);
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
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg(obj* x_0, obj* x_1) {
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
x_6 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg(x_2, x_1);
x_7 = lean::unbox_uint32(x_3);
x_8 = l_Char_quoteCore(x_7);
x_9 = l_Char_HasRepr___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_12 = lean::string_append(x_10, x_9);
x_13 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l___private_init_lean_parser_trie_7__toStringAux___main___rarg(x_4);
x_15 = lean::box(1);
x_16 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(x_14, x_15);
x_17 = lean::mk_nat_obj(2ul);
x_18 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = l_Lean_Format_group___main(x_18);
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
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::box(0);
x_3 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_7__toStringAux___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_7__toStringAux___main___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_7__toStringAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_7__toStringAux___main___rarg(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_7__toStringAux___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_7__toStringAux___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_parser_trie_7__toStringAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_HasToString___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l___private_init_lean_parser_trie_7__toStringAux___main___rarg(x_0);
x_2 = lean::box(1);
x_3 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(x_1, x_2);
x_4 = l_Lean_Options_empty;
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Trie_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_HasToString___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_HasToString___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_HasToString___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_Trie_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_lean_format(obj*);
obj* initialize_init_lean_parser_parsec(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_trie(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
 l_Lean_Parser_Trie_empty___closed__1 = _init_l_Lean_Parser_Trie_empty___closed__1();
lean::mark_persistent(l_Lean_Parser_Trie_empty___closed__1);
return w;
}

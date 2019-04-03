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
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux(obj*);
obj* l_Lean_Parser_Trie_Inhabited___boxed(obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___boxed(obj*);
obj* l_Lean_Parser_Trie_HasToString___rarg___boxed(obj*);
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___boxed(obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___boxed(obj*);
obj* l_Lean_Parser_Trie_find(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___boxed(obj*);
obj* l_String_OldIterator_remaining___main(obj*);
extern obj* l_Lean_Options_empty;
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___boxed(obj*);
obj* l_Lean_Parser_Trie_empty___boxed(obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___boxed(obj*);
obj* l_Lean_Parser_Trie_insert___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_Inhabited(obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc(obj*);
obj* l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___boxed(obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg(obj*, obj*);
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
obj* l_Lean_Parser_Trie_HasToString___rarg(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main___boxed(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l___private_init_lean_parser_trie_2__insertAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1;
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
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg(obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg___boxed(obj*, obj*);
obj* l_Lean_toFmt___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux(obj*);
obj* l_Lean_Parser_Trie_HasToString(obj*);
obj* l_Lean_Parser_Trie_insert___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg___boxed(obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix(obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux(obj*);
obj* l_Char_lt___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3___rarg___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__3(obj*);
obj* l_Lean_Parser_Trie_empty___closed__1;
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___boxed(obj*);
obj* l_Lean_Parser_Trie_insert(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
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
obj* _init_l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Char_lt___boxed), 2, 0);
return x_0;
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
uint32 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; 
x_10 = lean::string_utf8_get(x_0, x_3);
x_11 = lean::string_utf8_next(x_0, x_3);
x_12 = l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1;
x_13 = lean::box_uint32(x_10);
lean::inc(x_13);
lean::inc(x_6);
x_16 = l_RBNode_find___main___rarg(x_12, lean::box(0), x_6, x_13);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_0, x_1, x_11);
lean::dec(x_11);
x_19 = l_RBNode_insert___rarg(x_12, x_6, x_13, x_17);
if (lean::is_scalar(x_8)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_8;
}
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
x_24 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_0, x_1, x_21, x_11);
lean::dec(x_11);
x_26 = l_RBNode_insert___rarg(x_12, x_6, x_13, x_24);
if (lean::is_scalar(x_8)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_8;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_4);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_1);
if (lean::is_scalar(x_8)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_8;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_6);
return x_30;
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
uint32 x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_10 = lean::string_utf8_get(x_0, x_2);
x_11 = l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1;
x_12 = lean::box_uint32(x_10);
x_13 = l_RBNode_find___main___rarg(x_11, lean::box(0), x_5, x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; 
lean::dec(x_2);
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_1 = x_16;
x_2 = x_19;
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
lean::inc(x_2);
return x_2;
}
else
{
obj* x_5; 
x_5 = lean::alloc_cnstr(0, 2, 0);
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
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
obj* x_11; uint32 x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_2);
x_11 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_4, x_2, x_3);
lean::dec(x_3);
x_13 = lean::string_utf8_get(x_0, x_2);
x_14 = l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1;
x_15 = lean::box_uint32(x_13);
x_16 = l_RBNode_find___main___rarg(x_14, lean::box(0), x_6, x_15);
if (lean::obj_tag(x_16) == 0)
{
lean::dec(x_2);
return x_11;
}
else
{
obj* x_18; obj* x_21; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_21 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_1 = x_18;
x_2 = x_21;
x_3 = x_11;
goto _start;
}
}
else
{
obj* x_25; 
lean::dec(x_6);
x_25 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_4, x_2, x_3);
lean::dec(x_3);
return x_25;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_12; uint32 x_14; obj* x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = l_String_OldIterator_curr___main(x_2);
x_15 = l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1;
x_16 = lean::box_uint32(x_14);
x_17 = l_RBNode_find___main___rarg(x_15, lean::box(0), x_8, x_16);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_12);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_20;
x_2 = x_23;
goto _start;
}
}
else
{
obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_3);
x_26 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_28 = x_6;
} else {
 lean::inc(x_26);
 lean::dec(x_6);
 x_28 = lean::box(0);
}
lean::inc(x_2);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_2);
lean::cnstr_set(x_30, 1, x_26);
if (lean::is_scalar(x_28)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_28;
}
lean::cnstr_set(x_31, 0, x_30);
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_12);
lean::dec(x_2);
return x_31;
}
else
{
obj* x_34; obj* x_37; 
x_34 = lean::cnstr_get(x_17, 0);
lean::inc(x_34);
lean::dec(x_17);
x_37 = l_String_OldIterator_next___main(x_2);
x_0 = x_12;
x_1 = x_34;
x_2 = x_37;
x_3 = x_31;
goto _start;
}
}
}
else
{
obj* x_40; 
lean::dec(x_0);
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
if (lean::obj_tag(x_40) == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_3);
x_45 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_2);
lean::cnstr_set(x_48, 1, x_45);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
return x_49;
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
 l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1 = _init_l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1();
lean::mark_persistent(l___private_init_lean_parser_trie_2__insertAux___main___rarg___closed__1);
return w;
}

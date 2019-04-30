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
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(obj*);
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
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___boxed(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_Inhabited___boxed(obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(obj*);
obj* l_Lean_Parser_Trie_HasToString___rarg___boxed(obj*);
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__1(obj*, obj*);
uint32 l_String_OldIterator_curr___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___boxed(obj*);
obj* l_Lean_Parser_Trie_find(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___boxed(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1(obj*);
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4(obj*);
extern obj* l_Lean_Options_empty;
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(obj*, uint32, obj*);
obj* l_Lean_Parser_Trie_empty___boxed(obj*);
obj* l_Lean_Parser_Trie_insert___rarg(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Trie_Inhabited(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___boxed(obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Trie_find___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj*, obj*, obj*);
obj* l_String_OldIterator_next___main(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_3__findAux(obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3(obj*);
obj* l_Lean_Parser_Trie_HasEmptyc(obj*);
obj* l_Lean_Parser_Trie_HasToString___rarg(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main___boxed(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l___private_init_lean_parser_trie_2__insertAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main(obj*);
obj* l_Char_quoteCore(uint32);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_empty(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_7__toStringAux___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg(obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg___boxed(obj*, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux(obj*);
obj* l_Lean_Parser_Trie_HasToString(obj*);
obj* l_Lean_Parser_Trie_insert___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg___boxed(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___boxed(obj*);
obj* l_Lean_Parser_Trie_HasEmptyc___closed__1;
obj* l_Lean_Parser_Trie_matchPrefix(obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1(obj*);
obj* l_Lean_Parser_Trie_empty___closed__1;
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___boxed(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux___rarg(obj*);
obj* l_Lean_Parser_Trie_HasEmptyc___boxed(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___boxed(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___boxed(obj*);
obj* l___private_init_lean_parser_trie_6__oldMatchPrefixAux(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___boxed(obj*);
obj* l_Lean_Parser_Trie_insert(obj*);
obj* l___private_init_lean_parser_trie_7__toStringAux(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___boxed(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___boxed(obj*);
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
obj* _init_l_Lean_Parser_Trie_HasEmptyc___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_Trie_empty(lean::box(0));
return x_0;
}
}
obj* l_Lean_Parser_Trie_HasEmptyc(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_Trie_HasEmptyc___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_HasEmptyc(x_0);
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
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
x_24 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_14, x_1, x_2);
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
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_8, x_1, x_2);
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
x_47 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_36, x_1, x_2);
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
obj* x_50; 
x_50 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_36, x_1, x_2);
if (lean::obj_tag(x_50) == 0)
{
lean::dec(x_34);
lean::dec(x_38);
lean::dec(x_30);
return x_50;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; 
x_56 = lean::cnstr_get(x_50, 3);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_60; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_68; 
x_58 = lean::cnstr_get(x_50, 1);
x_60 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_62 = x_50;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_50);
 x_62 = lean::box(0);
}
x_63 = 0;
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_56);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_60);
lean::cnstr_set(x_64, 3, x_56);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_63);
x_65 = x_64;
x_66 = 1;
if (lean::is_scalar(x_38)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_38;
}
lean::cnstr_set(x_67, 0, x_30);
lean::cnstr_set(x_67, 1, x_32);
lean::cnstr_set(x_67, 2, x_34);
lean::cnstr_set(x_67, 3, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_66);
x_68 = x_67;
return x_68;
}
else
{
uint8 x_69; 
x_69 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*4);
if (x_69 == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_70 = lean::cnstr_get(x_50, 1);
x_72 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_74 = x_50;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_50);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_56, 0);
x_77 = lean::cnstr_get(x_56, 1);
x_79 = lean::cnstr_get(x_56, 2);
x_81 = lean::cnstr_get(x_56, 3);
if (lean::is_exclusive(x_56)) {
 x_83 = x_56;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_56);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_30);
lean::cnstr_set(x_85, 1, x_32);
lean::cnstr_set(x_85, 2, x_34);
lean::cnstr_set(x_85, 3, x_54);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
if (lean::is_scalar(x_74)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_74;
}
lean::cnstr_set(x_87, 0, x_75);
lean::cnstr_set(x_87, 1, x_77);
lean::cnstr_set(x_87, 2, x_79);
lean::cnstr_set(x_87, 3, x_81);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_84);
x_88 = x_87;
if (lean::is_scalar(x_38)) {
 x_89 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_89 = x_38;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_70);
lean::cnstr_set(x_89, 2, x_72);
lean::cnstr_set(x_89, 3, x_88);
lean::cnstr_set_scalar(x_89, sizeof(void*)*4, x_69);
x_90 = x_89;
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_91 = lean::cnstr_get(x_50, 1);
x_93 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_95 = x_50;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_50);
 x_95 = lean::box(0);
}
x_96 = 0;
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_54);
lean::cnstr_set(x_97, 1, x_91);
lean::cnstr_set(x_97, 2, x_93);
lean::cnstr_set(x_97, 3, x_56);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_96);
x_98 = x_97;
if (lean::is_scalar(x_38)) {
 x_99 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_99 = x_38;
}
lean::cnstr_set(x_99, 0, x_30);
lean::cnstr_set(x_99, 1, x_32);
lean::cnstr_set(x_99, 2, x_34);
lean::cnstr_set(x_99, 3, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_69);
x_100 = x_99;
return x_100;
}
}
}
else
{
uint8 x_101; 
x_101 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_101 == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_102 = lean::cnstr_get(x_50, 1);
x_104 = lean::cnstr_get(x_50, 2);
x_106 = lean::cnstr_get(x_50, 3);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_108 = x_50;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_50);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_54, 0);
x_111 = lean::cnstr_get(x_54, 1);
x_113 = lean::cnstr_get(x_54, 2);
x_115 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_117 = x_54;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_54);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_30);
lean::cnstr_set(x_119, 1, x_32);
lean::cnstr_set(x_119, 2, x_34);
lean::cnstr_set(x_119, 3, x_109);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = x_119;
if (lean::is_scalar(x_108)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_108;
}
lean::cnstr_set(x_121, 0, x_115);
lean::cnstr_set(x_121, 1, x_102);
lean::cnstr_set(x_121, 2, x_104);
lean::cnstr_set(x_121, 3, x_106);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_118);
x_122 = x_121;
if (lean::is_scalar(x_38)) {
 x_123 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_123 = x_38;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_111);
lean::cnstr_set(x_123, 2, x_113);
lean::cnstr_set(x_123, 3, x_122);
lean::cnstr_set_scalar(x_123, sizeof(void*)*4, x_101);
x_124 = x_123;
return x_124;
}
else
{
obj* x_125; 
x_125 = lean::cnstr_get(x_50, 3);
lean::inc(x_125);
if (lean::obj_tag(x_125) == 0)
{
obj* x_127; obj* x_129; obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_127 = lean::cnstr_get(x_50, 1);
x_129 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_131 = x_50;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_50);
 x_131 = lean::box(0);
}
x_132 = 0;
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_54);
lean::cnstr_set(x_133, 1, x_127);
lean::cnstr_set(x_133, 2, x_129);
lean::cnstr_set(x_133, 3, x_125);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_132);
x_134 = x_133;
if (lean::is_scalar(x_38)) {
 x_135 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_135 = x_38;
}
lean::cnstr_set(x_135, 0, x_30);
lean::cnstr_set(x_135, 1, x_32);
lean::cnstr_set(x_135, 2, x_34);
lean::cnstr_set(x_135, 3, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*4, x_101);
x_136 = x_135;
return x_136;
}
else
{
uint8 x_137; 
x_137 = lean::cnstr_get_scalar<uint8>(x_125, sizeof(void*)*4);
if (x_137 == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_38);
x_139 = lean::cnstr_get(x_50, 1);
x_141 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_143 = x_50;
} else {
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_50);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_125, 0);
x_146 = lean::cnstr_get(x_125, 1);
x_148 = lean::cnstr_get(x_125, 2);
x_150 = lean::cnstr_get(x_125, 3);
if (lean::is_exclusive(x_125)) {
 x_152 = x_125;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::inc(x_150);
 lean::dec(x_125);
 x_152 = lean::box(0);
}
lean::inc(x_54);
if (lean::is_scalar(x_152)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_152;
}
lean::cnstr_set(x_154, 0, x_30);
lean::cnstr_set(x_154, 1, x_32);
lean::cnstr_set(x_154, 2, x_34);
lean::cnstr_set(x_154, 3, x_54);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 lean::cnstr_release(x_54, 2);
 lean::cnstr_release(x_54, 3);
 x_155 = x_54;
} else {
 lean::dec(x_54);
 x_155 = lean::box(0);
}
lean::cnstr_set_scalar(x_154, sizeof(void*)*4, x_101);
x_156 = x_154;
if (lean::is_scalar(x_155)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_155;
}
lean::cnstr_set(x_157, 0, x_144);
lean::cnstr_set(x_157, 1, x_146);
lean::cnstr_set(x_157, 2, x_148);
lean::cnstr_set(x_157, 3, x_150);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_101);
x_158 = x_157;
if (lean::is_scalar(x_143)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_143;
}
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_139);
lean::cnstr_set(x_159, 2, x_141);
lean::cnstr_set(x_159, 3, x_158);
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_137);
x_160 = x_159;
return x_160;
}
else
{
obj* x_161; obj* x_163; obj* x_165; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_176; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_161 = lean::cnstr_get(x_50, 1);
x_163 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_165 = x_50;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_50);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_54, 0);
x_168 = lean::cnstr_get(x_54, 1);
x_170 = lean::cnstr_get(x_54, 2);
x_172 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_174 = x_54;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::inc(x_172);
 lean::dec(x_54);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_166);
lean::cnstr_set(x_175, 1, x_168);
lean::cnstr_set(x_175, 2, x_170);
lean::cnstr_set(x_175, 3, x_172);
lean::cnstr_set_scalar(x_175, sizeof(void*)*4, x_137);
x_176 = x_175;
x_177 = 0;
if (lean::is_scalar(x_165)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_165;
}
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_161);
lean::cnstr_set(x_178, 2, x_163);
lean::cnstr_set(x_178, 3, x_125);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_177);
x_179 = x_178;
if (lean::is_scalar(x_38)) {
 x_180 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_180 = x_38;
}
lean::cnstr_set(x_180, 0, x_30);
lean::cnstr_set(x_180, 1, x_32);
lean::cnstr_set(x_180, 2, x_34);
lean::cnstr_set(x_180, 3, x_179);
lean::cnstr_set_scalar(x_180, sizeof(void*)*4, x_137);
x_181 = x_180;
return x_181;
}
}
}
}
}
}
}
}
else
{
uint8 x_182; 
x_182 = l_RBNode_isRed___main___rarg(x_30);
if (x_182 == 0)
{
obj* x_183; obj* x_184; obj* x_185; 
x_183 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_184 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_184 = x_38;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_32);
lean::cnstr_set(x_184, 2, x_34);
lean::cnstr_set(x_184, 3, x_36);
lean::cnstr_set_scalar(x_184, sizeof(void*)*4, x_7);
x_185 = x_184;
return x_185;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_30, x_1, x_2);
if (lean::obj_tag(x_186) == 0)
{
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_38);
return x_186;
}
else
{
obj* x_190; 
x_190 = lean::cnstr_get(x_186, 0);
lean::inc(x_190);
if (lean::obj_tag(x_190) == 0)
{
obj* x_192; 
x_192 = lean::cnstr_get(x_186, 3);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_194; obj* x_196; obj* x_198; uint8 x_199; obj* x_200; obj* x_201; uint8 x_202; obj* x_203; obj* x_204; 
x_194 = lean::cnstr_get(x_186, 1);
x_196 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_198 = x_186;
} else {
 lean::inc(x_194);
 lean::inc(x_196);
 lean::dec(x_186);
 x_198 = lean::box(0);
}
x_199 = 0;
if (lean::is_scalar(x_198)) {
 x_200 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_200 = x_198;
}
lean::cnstr_set(x_200, 0, x_192);
lean::cnstr_set(x_200, 1, x_194);
lean::cnstr_set(x_200, 2, x_196);
lean::cnstr_set(x_200, 3, x_192);
lean::cnstr_set_scalar(x_200, sizeof(void*)*4, x_199);
x_201 = x_200;
x_202 = 1;
if (lean::is_scalar(x_38)) {
 x_203 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_203 = x_38;
}
lean::cnstr_set(x_203, 0, x_201);
lean::cnstr_set(x_203, 1, x_32);
lean::cnstr_set(x_203, 2, x_34);
lean::cnstr_set(x_203, 3, x_36);
lean::cnstr_set_scalar(x_203, sizeof(void*)*4, x_202);
x_204 = x_203;
return x_204;
}
else
{
uint8 x_205; 
x_205 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*4);
if (x_205 == 0)
{
obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_206 = lean::cnstr_get(x_186, 1);
x_208 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_210 = x_186;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_186);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_192, 0);
x_213 = lean::cnstr_get(x_192, 1);
x_215 = lean::cnstr_get(x_192, 2);
x_217 = lean::cnstr_get(x_192, 3);
if (lean::is_exclusive(x_192)) {
 x_219 = x_192;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::inc(x_215);
 lean::inc(x_217);
 lean::dec(x_192);
 x_219 = lean::box(0);
}
x_220 = 1;
if (lean::is_scalar(x_219)) {
 x_221 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_221 = x_219;
}
lean::cnstr_set(x_221, 0, x_190);
lean::cnstr_set(x_221, 1, x_206);
lean::cnstr_set(x_221, 2, x_208);
lean::cnstr_set(x_221, 3, x_211);
lean::cnstr_set_scalar(x_221, sizeof(void*)*4, x_220);
x_222 = x_221;
if (lean::is_scalar(x_210)) {
 x_223 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_223 = x_210;
}
lean::cnstr_set(x_223, 0, x_217);
lean::cnstr_set(x_223, 1, x_32);
lean::cnstr_set(x_223, 2, x_34);
lean::cnstr_set(x_223, 3, x_36);
lean::cnstr_set_scalar(x_223, sizeof(void*)*4, x_220);
x_224 = x_223;
if (lean::is_scalar(x_38)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_38;
}
lean::cnstr_set(x_225, 0, x_222);
lean::cnstr_set(x_225, 1, x_213);
lean::cnstr_set(x_225, 2, x_215);
lean::cnstr_set(x_225, 3, x_224);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_205);
x_226 = x_225;
return x_226;
}
else
{
obj* x_227; obj* x_229; obj* x_231; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_227 = lean::cnstr_get(x_186, 1);
x_229 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_231 = x_186;
} else {
 lean::inc(x_227);
 lean::inc(x_229);
 lean::dec(x_186);
 x_231 = lean::box(0);
}
x_232 = 0;
if (lean::is_scalar(x_231)) {
 x_233 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_233 = x_231;
}
lean::cnstr_set(x_233, 0, x_190);
lean::cnstr_set(x_233, 1, x_227);
lean::cnstr_set(x_233, 2, x_229);
lean::cnstr_set(x_233, 3, x_192);
lean::cnstr_set_scalar(x_233, sizeof(void*)*4, x_232);
x_234 = x_233;
if (lean::is_scalar(x_38)) {
 x_235 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_235 = x_38;
}
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set(x_235, 1, x_32);
lean::cnstr_set(x_235, 2, x_34);
lean::cnstr_set(x_235, 3, x_36);
lean::cnstr_set_scalar(x_235, sizeof(void*)*4, x_205);
x_236 = x_235;
return x_236;
}
}
}
else
{
uint8 x_237; 
x_237 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*4);
if (x_237 == 0)
{
obj* x_238; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_251; obj* x_253; uint8 x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_238 = lean::cnstr_get(x_186, 1);
x_240 = lean::cnstr_get(x_186, 2);
x_242 = lean::cnstr_get(x_186, 3);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 x_244 = x_186;
} else {
 lean::inc(x_238);
 lean::inc(x_240);
 lean::inc(x_242);
 lean::dec(x_186);
 x_244 = lean::box(0);
}
x_245 = lean::cnstr_get(x_190, 0);
x_247 = lean::cnstr_get(x_190, 1);
x_249 = lean::cnstr_get(x_190, 2);
x_251 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_253 = x_190;
} else {
 lean::inc(x_245);
 lean::inc(x_247);
 lean::inc(x_249);
 lean::inc(x_251);
 lean::dec(x_190);
 x_253 = lean::box(0);
}
x_254 = 1;
if (lean::is_scalar(x_253)) {
 x_255 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_255 = x_253;
}
lean::cnstr_set(x_255, 0, x_245);
lean::cnstr_set(x_255, 1, x_247);
lean::cnstr_set(x_255, 2, x_249);
lean::cnstr_set(x_255, 3, x_251);
lean::cnstr_set_scalar(x_255, sizeof(void*)*4, x_254);
x_256 = x_255;
if (lean::is_scalar(x_244)) {
 x_257 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_257 = x_244;
}
lean::cnstr_set(x_257, 0, x_242);
lean::cnstr_set(x_257, 1, x_32);
lean::cnstr_set(x_257, 2, x_34);
lean::cnstr_set(x_257, 3, x_36);
lean::cnstr_set_scalar(x_257, sizeof(void*)*4, x_254);
x_258 = x_257;
if (lean::is_scalar(x_38)) {
 x_259 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_259 = x_38;
}
lean::cnstr_set(x_259, 0, x_256);
lean::cnstr_set(x_259, 1, x_238);
lean::cnstr_set(x_259, 2, x_240);
lean::cnstr_set(x_259, 3, x_258);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_237);
x_260 = x_259;
return x_260;
}
else
{
obj* x_261; 
x_261 = lean::cnstr_get(x_186, 3);
lean::inc(x_261);
if (lean::obj_tag(x_261) == 0)
{
obj* x_263; obj* x_265; obj* x_267; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_263 = lean::cnstr_get(x_186, 1);
x_265 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_267 = x_186;
} else {
 lean::inc(x_263);
 lean::inc(x_265);
 lean::dec(x_186);
 x_267 = lean::box(0);
}
x_268 = 0;
if (lean::is_scalar(x_267)) {
 x_269 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_269 = x_267;
}
lean::cnstr_set(x_269, 0, x_190);
lean::cnstr_set(x_269, 1, x_263);
lean::cnstr_set(x_269, 2, x_265);
lean::cnstr_set(x_269, 3, x_261);
lean::cnstr_set_scalar(x_269, sizeof(void*)*4, x_268);
x_270 = x_269;
if (lean::is_scalar(x_38)) {
 x_271 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_271 = x_38;
}
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_32);
lean::cnstr_set(x_271, 2, x_34);
lean::cnstr_set(x_271, 3, x_36);
lean::cnstr_set_scalar(x_271, sizeof(void*)*4, x_237);
x_272 = x_271;
return x_272;
}
else
{
uint8 x_273; 
x_273 = lean::cnstr_get_scalar<uint8>(x_261, sizeof(void*)*4);
if (x_273 == 0)
{
obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_286; obj* x_288; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_38);
x_275 = lean::cnstr_get(x_186, 1);
x_277 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_279 = x_186;
} else {
 lean::inc(x_275);
 lean::inc(x_277);
 lean::dec(x_186);
 x_279 = lean::box(0);
}
x_280 = lean::cnstr_get(x_261, 0);
x_282 = lean::cnstr_get(x_261, 1);
x_284 = lean::cnstr_get(x_261, 2);
x_286 = lean::cnstr_get(x_261, 3);
if (lean::is_exclusive(x_261)) {
 x_288 = x_261;
} else {
 lean::inc(x_280);
 lean::inc(x_282);
 lean::inc(x_284);
 lean::inc(x_286);
 lean::dec(x_261);
 x_288 = lean::box(0);
}
lean::inc(x_190);
if (lean::is_scalar(x_288)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_288;
}
lean::cnstr_set(x_290, 0, x_190);
lean::cnstr_set(x_290, 1, x_275);
lean::cnstr_set(x_290, 2, x_277);
lean::cnstr_set(x_290, 3, x_280);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 lean::cnstr_release(x_190, 2);
 lean::cnstr_release(x_190, 3);
 x_291 = x_190;
} else {
 lean::dec(x_190);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_237);
x_292 = x_290;
if (lean::is_scalar(x_291)) {
 x_293 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_293 = x_291;
}
lean::cnstr_set(x_293, 0, x_286);
lean::cnstr_set(x_293, 1, x_32);
lean::cnstr_set(x_293, 2, x_34);
lean::cnstr_set(x_293, 3, x_36);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_237);
x_294 = x_293;
if (lean::is_scalar(x_279)) {
 x_295 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_295 = x_279;
}
lean::cnstr_set(x_295, 0, x_292);
lean::cnstr_set(x_295, 1, x_282);
lean::cnstr_set(x_295, 2, x_284);
lean::cnstr_set(x_295, 3, x_294);
lean::cnstr_set_scalar(x_295, sizeof(void*)*4, x_273);
x_296 = x_295;
return x_296;
}
else
{
obj* x_297; obj* x_299; obj* x_301; obj* x_302; obj* x_304; obj* x_306; obj* x_308; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_297 = lean::cnstr_get(x_186, 1);
x_299 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_301 = x_186;
} else {
 lean::inc(x_297);
 lean::inc(x_299);
 lean::dec(x_186);
 x_301 = lean::box(0);
}
x_302 = lean::cnstr_get(x_190, 0);
x_304 = lean::cnstr_get(x_190, 1);
x_306 = lean::cnstr_get(x_190, 2);
x_308 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_310 = x_190;
} else {
 lean::inc(x_302);
 lean::inc(x_304);
 lean::inc(x_306);
 lean::inc(x_308);
 lean::dec(x_190);
 x_310 = lean::box(0);
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_302);
lean::cnstr_set(x_311, 1, x_304);
lean::cnstr_set(x_311, 2, x_306);
lean::cnstr_set(x_311, 3, x_308);
lean::cnstr_set_scalar(x_311, sizeof(void*)*4, x_273);
x_312 = x_311;
x_313 = 0;
if (lean::is_scalar(x_301)) {
 x_314 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_314 = x_301;
}
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_297);
lean::cnstr_set(x_314, 2, x_299);
lean::cnstr_set(x_314, 3, x_261);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
x_315 = x_314;
if (lean::is_scalar(x_38)) {
 x_316 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_316 = x_38;
}
lean::cnstr_set(x_316, 0, x_315);
lean::cnstr_set(x_316, 1, x_32);
lean::cnstr_set(x_316, 2, x_34);
lean::cnstr_set(x_316, 3, x_36);
lean::cnstr_set_scalar(x_316, sizeof(void*)*4, x_273);
x_317 = x_316;
return x_317;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed), 3, 0);
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
obj* x_50; 
x_50 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_36, x_1, x_2);
if (lean::obj_tag(x_50) == 0)
{
lean::dec(x_34);
lean::dec(x_38);
lean::dec(x_30);
return x_50;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; 
x_56 = lean::cnstr_get(x_50, 3);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_60; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_68; 
x_58 = lean::cnstr_get(x_50, 1);
x_60 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_62 = x_50;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_50);
 x_62 = lean::box(0);
}
x_63 = 0;
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_56);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_60);
lean::cnstr_set(x_64, 3, x_56);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_63);
x_65 = x_64;
x_66 = 1;
if (lean::is_scalar(x_38)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_38;
}
lean::cnstr_set(x_67, 0, x_30);
lean::cnstr_set(x_67, 1, x_32);
lean::cnstr_set(x_67, 2, x_34);
lean::cnstr_set(x_67, 3, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_66);
x_68 = x_67;
return x_68;
}
else
{
uint8 x_69; 
x_69 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*4);
if (x_69 == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_70 = lean::cnstr_get(x_50, 1);
x_72 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_74 = x_50;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_50);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_56, 0);
x_77 = lean::cnstr_get(x_56, 1);
x_79 = lean::cnstr_get(x_56, 2);
x_81 = lean::cnstr_get(x_56, 3);
if (lean::is_exclusive(x_56)) {
 x_83 = x_56;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_56);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_30);
lean::cnstr_set(x_85, 1, x_32);
lean::cnstr_set(x_85, 2, x_34);
lean::cnstr_set(x_85, 3, x_54);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
if (lean::is_scalar(x_74)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_74;
}
lean::cnstr_set(x_87, 0, x_75);
lean::cnstr_set(x_87, 1, x_77);
lean::cnstr_set(x_87, 2, x_79);
lean::cnstr_set(x_87, 3, x_81);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_84);
x_88 = x_87;
if (lean::is_scalar(x_38)) {
 x_89 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_89 = x_38;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_70);
lean::cnstr_set(x_89, 2, x_72);
lean::cnstr_set(x_89, 3, x_88);
lean::cnstr_set_scalar(x_89, sizeof(void*)*4, x_69);
x_90 = x_89;
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_91 = lean::cnstr_get(x_50, 1);
x_93 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_95 = x_50;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_50);
 x_95 = lean::box(0);
}
x_96 = 0;
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_54);
lean::cnstr_set(x_97, 1, x_91);
lean::cnstr_set(x_97, 2, x_93);
lean::cnstr_set(x_97, 3, x_56);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_96);
x_98 = x_97;
if (lean::is_scalar(x_38)) {
 x_99 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_99 = x_38;
}
lean::cnstr_set(x_99, 0, x_30);
lean::cnstr_set(x_99, 1, x_32);
lean::cnstr_set(x_99, 2, x_34);
lean::cnstr_set(x_99, 3, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_69);
x_100 = x_99;
return x_100;
}
}
}
else
{
uint8 x_101; 
x_101 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_101 == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_102 = lean::cnstr_get(x_50, 1);
x_104 = lean::cnstr_get(x_50, 2);
x_106 = lean::cnstr_get(x_50, 3);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_108 = x_50;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_50);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_54, 0);
x_111 = lean::cnstr_get(x_54, 1);
x_113 = lean::cnstr_get(x_54, 2);
x_115 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_117 = x_54;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_54);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_30);
lean::cnstr_set(x_119, 1, x_32);
lean::cnstr_set(x_119, 2, x_34);
lean::cnstr_set(x_119, 3, x_109);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = x_119;
if (lean::is_scalar(x_108)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_108;
}
lean::cnstr_set(x_121, 0, x_115);
lean::cnstr_set(x_121, 1, x_102);
lean::cnstr_set(x_121, 2, x_104);
lean::cnstr_set(x_121, 3, x_106);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_118);
x_122 = x_121;
if (lean::is_scalar(x_38)) {
 x_123 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_123 = x_38;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_111);
lean::cnstr_set(x_123, 2, x_113);
lean::cnstr_set(x_123, 3, x_122);
lean::cnstr_set_scalar(x_123, sizeof(void*)*4, x_101);
x_124 = x_123;
return x_124;
}
else
{
obj* x_125; 
x_125 = lean::cnstr_get(x_50, 3);
lean::inc(x_125);
if (lean::obj_tag(x_125) == 0)
{
obj* x_127; obj* x_129; obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_127 = lean::cnstr_get(x_50, 1);
x_129 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_131 = x_50;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_50);
 x_131 = lean::box(0);
}
x_132 = 0;
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_54);
lean::cnstr_set(x_133, 1, x_127);
lean::cnstr_set(x_133, 2, x_129);
lean::cnstr_set(x_133, 3, x_125);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_132);
x_134 = x_133;
if (lean::is_scalar(x_38)) {
 x_135 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_135 = x_38;
}
lean::cnstr_set(x_135, 0, x_30);
lean::cnstr_set(x_135, 1, x_32);
lean::cnstr_set(x_135, 2, x_34);
lean::cnstr_set(x_135, 3, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*4, x_101);
x_136 = x_135;
return x_136;
}
else
{
uint8 x_137; 
x_137 = lean::cnstr_get_scalar<uint8>(x_125, sizeof(void*)*4);
if (x_137 == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_38);
x_139 = lean::cnstr_get(x_50, 1);
x_141 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_143 = x_50;
} else {
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_50);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_125, 0);
x_146 = lean::cnstr_get(x_125, 1);
x_148 = lean::cnstr_get(x_125, 2);
x_150 = lean::cnstr_get(x_125, 3);
if (lean::is_exclusive(x_125)) {
 x_152 = x_125;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::inc(x_150);
 lean::dec(x_125);
 x_152 = lean::box(0);
}
lean::inc(x_54);
if (lean::is_scalar(x_152)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_152;
}
lean::cnstr_set(x_154, 0, x_30);
lean::cnstr_set(x_154, 1, x_32);
lean::cnstr_set(x_154, 2, x_34);
lean::cnstr_set(x_154, 3, x_54);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 lean::cnstr_release(x_54, 2);
 lean::cnstr_release(x_54, 3);
 x_155 = x_54;
} else {
 lean::dec(x_54);
 x_155 = lean::box(0);
}
lean::cnstr_set_scalar(x_154, sizeof(void*)*4, x_101);
x_156 = x_154;
if (lean::is_scalar(x_155)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_155;
}
lean::cnstr_set(x_157, 0, x_144);
lean::cnstr_set(x_157, 1, x_146);
lean::cnstr_set(x_157, 2, x_148);
lean::cnstr_set(x_157, 3, x_150);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_101);
x_158 = x_157;
if (lean::is_scalar(x_143)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_143;
}
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_139);
lean::cnstr_set(x_159, 2, x_141);
lean::cnstr_set(x_159, 3, x_158);
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_137);
x_160 = x_159;
return x_160;
}
else
{
obj* x_161; obj* x_163; obj* x_165; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_176; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_161 = lean::cnstr_get(x_50, 1);
x_163 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_165 = x_50;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_50);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_54, 0);
x_168 = lean::cnstr_get(x_54, 1);
x_170 = lean::cnstr_get(x_54, 2);
x_172 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_174 = x_54;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::inc(x_172);
 lean::dec(x_54);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_166);
lean::cnstr_set(x_175, 1, x_168);
lean::cnstr_set(x_175, 2, x_170);
lean::cnstr_set(x_175, 3, x_172);
lean::cnstr_set_scalar(x_175, sizeof(void*)*4, x_137);
x_176 = x_175;
x_177 = 0;
if (lean::is_scalar(x_165)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_165;
}
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_161);
lean::cnstr_set(x_178, 2, x_163);
lean::cnstr_set(x_178, 3, x_125);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_177);
x_179 = x_178;
if (lean::is_scalar(x_38)) {
 x_180 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_180 = x_38;
}
lean::cnstr_set(x_180, 0, x_30);
lean::cnstr_set(x_180, 1, x_32);
lean::cnstr_set(x_180, 2, x_34);
lean::cnstr_set(x_180, 3, x_179);
lean::cnstr_set_scalar(x_180, sizeof(void*)*4, x_137);
x_181 = x_180;
return x_181;
}
}
}
}
}
}
}
}
else
{
uint8 x_182; 
x_182 = l_RBNode_isRed___main___rarg(x_30);
if (x_182 == 0)
{
obj* x_183; obj* x_184; obj* x_185; 
x_183 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_184 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_184 = x_38;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_32);
lean::cnstr_set(x_184, 2, x_34);
lean::cnstr_set(x_184, 3, x_36);
lean::cnstr_set_scalar(x_184, sizeof(void*)*4, x_7);
x_185 = x_184;
return x_185;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_30, x_1, x_2);
if (lean::obj_tag(x_186) == 0)
{
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_38);
return x_186;
}
else
{
obj* x_190; 
x_190 = lean::cnstr_get(x_186, 0);
lean::inc(x_190);
if (lean::obj_tag(x_190) == 0)
{
obj* x_192; 
x_192 = lean::cnstr_get(x_186, 3);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_194; obj* x_196; obj* x_198; uint8 x_199; obj* x_200; obj* x_201; uint8 x_202; obj* x_203; obj* x_204; 
x_194 = lean::cnstr_get(x_186, 1);
x_196 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_198 = x_186;
} else {
 lean::inc(x_194);
 lean::inc(x_196);
 lean::dec(x_186);
 x_198 = lean::box(0);
}
x_199 = 0;
if (lean::is_scalar(x_198)) {
 x_200 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_200 = x_198;
}
lean::cnstr_set(x_200, 0, x_192);
lean::cnstr_set(x_200, 1, x_194);
lean::cnstr_set(x_200, 2, x_196);
lean::cnstr_set(x_200, 3, x_192);
lean::cnstr_set_scalar(x_200, sizeof(void*)*4, x_199);
x_201 = x_200;
x_202 = 1;
if (lean::is_scalar(x_38)) {
 x_203 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_203 = x_38;
}
lean::cnstr_set(x_203, 0, x_201);
lean::cnstr_set(x_203, 1, x_32);
lean::cnstr_set(x_203, 2, x_34);
lean::cnstr_set(x_203, 3, x_36);
lean::cnstr_set_scalar(x_203, sizeof(void*)*4, x_202);
x_204 = x_203;
return x_204;
}
else
{
uint8 x_205; 
x_205 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*4);
if (x_205 == 0)
{
obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_206 = lean::cnstr_get(x_186, 1);
x_208 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_210 = x_186;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_186);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_192, 0);
x_213 = lean::cnstr_get(x_192, 1);
x_215 = lean::cnstr_get(x_192, 2);
x_217 = lean::cnstr_get(x_192, 3);
if (lean::is_exclusive(x_192)) {
 x_219 = x_192;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::inc(x_215);
 lean::inc(x_217);
 lean::dec(x_192);
 x_219 = lean::box(0);
}
x_220 = 1;
if (lean::is_scalar(x_219)) {
 x_221 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_221 = x_219;
}
lean::cnstr_set(x_221, 0, x_190);
lean::cnstr_set(x_221, 1, x_206);
lean::cnstr_set(x_221, 2, x_208);
lean::cnstr_set(x_221, 3, x_211);
lean::cnstr_set_scalar(x_221, sizeof(void*)*4, x_220);
x_222 = x_221;
if (lean::is_scalar(x_210)) {
 x_223 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_223 = x_210;
}
lean::cnstr_set(x_223, 0, x_217);
lean::cnstr_set(x_223, 1, x_32);
lean::cnstr_set(x_223, 2, x_34);
lean::cnstr_set(x_223, 3, x_36);
lean::cnstr_set_scalar(x_223, sizeof(void*)*4, x_220);
x_224 = x_223;
if (lean::is_scalar(x_38)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_38;
}
lean::cnstr_set(x_225, 0, x_222);
lean::cnstr_set(x_225, 1, x_213);
lean::cnstr_set(x_225, 2, x_215);
lean::cnstr_set(x_225, 3, x_224);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_205);
x_226 = x_225;
return x_226;
}
else
{
obj* x_227; obj* x_229; obj* x_231; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_227 = lean::cnstr_get(x_186, 1);
x_229 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_231 = x_186;
} else {
 lean::inc(x_227);
 lean::inc(x_229);
 lean::dec(x_186);
 x_231 = lean::box(0);
}
x_232 = 0;
if (lean::is_scalar(x_231)) {
 x_233 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_233 = x_231;
}
lean::cnstr_set(x_233, 0, x_190);
lean::cnstr_set(x_233, 1, x_227);
lean::cnstr_set(x_233, 2, x_229);
lean::cnstr_set(x_233, 3, x_192);
lean::cnstr_set_scalar(x_233, sizeof(void*)*4, x_232);
x_234 = x_233;
if (lean::is_scalar(x_38)) {
 x_235 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_235 = x_38;
}
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set(x_235, 1, x_32);
lean::cnstr_set(x_235, 2, x_34);
lean::cnstr_set(x_235, 3, x_36);
lean::cnstr_set_scalar(x_235, sizeof(void*)*4, x_205);
x_236 = x_235;
return x_236;
}
}
}
else
{
uint8 x_237; 
x_237 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*4);
if (x_237 == 0)
{
obj* x_238; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_251; obj* x_253; uint8 x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_238 = lean::cnstr_get(x_186, 1);
x_240 = lean::cnstr_get(x_186, 2);
x_242 = lean::cnstr_get(x_186, 3);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 x_244 = x_186;
} else {
 lean::inc(x_238);
 lean::inc(x_240);
 lean::inc(x_242);
 lean::dec(x_186);
 x_244 = lean::box(0);
}
x_245 = lean::cnstr_get(x_190, 0);
x_247 = lean::cnstr_get(x_190, 1);
x_249 = lean::cnstr_get(x_190, 2);
x_251 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_253 = x_190;
} else {
 lean::inc(x_245);
 lean::inc(x_247);
 lean::inc(x_249);
 lean::inc(x_251);
 lean::dec(x_190);
 x_253 = lean::box(0);
}
x_254 = 1;
if (lean::is_scalar(x_253)) {
 x_255 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_255 = x_253;
}
lean::cnstr_set(x_255, 0, x_245);
lean::cnstr_set(x_255, 1, x_247);
lean::cnstr_set(x_255, 2, x_249);
lean::cnstr_set(x_255, 3, x_251);
lean::cnstr_set_scalar(x_255, sizeof(void*)*4, x_254);
x_256 = x_255;
if (lean::is_scalar(x_244)) {
 x_257 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_257 = x_244;
}
lean::cnstr_set(x_257, 0, x_242);
lean::cnstr_set(x_257, 1, x_32);
lean::cnstr_set(x_257, 2, x_34);
lean::cnstr_set(x_257, 3, x_36);
lean::cnstr_set_scalar(x_257, sizeof(void*)*4, x_254);
x_258 = x_257;
if (lean::is_scalar(x_38)) {
 x_259 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_259 = x_38;
}
lean::cnstr_set(x_259, 0, x_256);
lean::cnstr_set(x_259, 1, x_238);
lean::cnstr_set(x_259, 2, x_240);
lean::cnstr_set(x_259, 3, x_258);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_237);
x_260 = x_259;
return x_260;
}
else
{
obj* x_261; 
x_261 = lean::cnstr_get(x_186, 3);
lean::inc(x_261);
if (lean::obj_tag(x_261) == 0)
{
obj* x_263; obj* x_265; obj* x_267; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_263 = lean::cnstr_get(x_186, 1);
x_265 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_267 = x_186;
} else {
 lean::inc(x_263);
 lean::inc(x_265);
 lean::dec(x_186);
 x_267 = lean::box(0);
}
x_268 = 0;
if (lean::is_scalar(x_267)) {
 x_269 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_269 = x_267;
}
lean::cnstr_set(x_269, 0, x_190);
lean::cnstr_set(x_269, 1, x_263);
lean::cnstr_set(x_269, 2, x_265);
lean::cnstr_set(x_269, 3, x_261);
lean::cnstr_set_scalar(x_269, sizeof(void*)*4, x_268);
x_270 = x_269;
if (lean::is_scalar(x_38)) {
 x_271 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_271 = x_38;
}
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_32);
lean::cnstr_set(x_271, 2, x_34);
lean::cnstr_set(x_271, 3, x_36);
lean::cnstr_set_scalar(x_271, sizeof(void*)*4, x_237);
x_272 = x_271;
return x_272;
}
else
{
uint8 x_273; 
x_273 = lean::cnstr_get_scalar<uint8>(x_261, sizeof(void*)*4);
if (x_273 == 0)
{
obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_286; obj* x_288; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_38);
x_275 = lean::cnstr_get(x_186, 1);
x_277 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_279 = x_186;
} else {
 lean::inc(x_275);
 lean::inc(x_277);
 lean::dec(x_186);
 x_279 = lean::box(0);
}
x_280 = lean::cnstr_get(x_261, 0);
x_282 = lean::cnstr_get(x_261, 1);
x_284 = lean::cnstr_get(x_261, 2);
x_286 = lean::cnstr_get(x_261, 3);
if (lean::is_exclusive(x_261)) {
 x_288 = x_261;
} else {
 lean::inc(x_280);
 lean::inc(x_282);
 lean::inc(x_284);
 lean::inc(x_286);
 lean::dec(x_261);
 x_288 = lean::box(0);
}
lean::inc(x_190);
if (lean::is_scalar(x_288)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_288;
}
lean::cnstr_set(x_290, 0, x_190);
lean::cnstr_set(x_290, 1, x_275);
lean::cnstr_set(x_290, 2, x_277);
lean::cnstr_set(x_290, 3, x_280);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 lean::cnstr_release(x_190, 2);
 lean::cnstr_release(x_190, 3);
 x_291 = x_190;
} else {
 lean::dec(x_190);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_237);
x_292 = x_290;
if (lean::is_scalar(x_291)) {
 x_293 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_293 = x_291;
}
lean::cnstr_set(x_293, 0, x_286);
lean::cnstr_set(x_293, 1, x_32);
lean::cnstr_set(x_293, 2, x_34);
lean::cnstr_set(x_293, 3, x_36);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_237);
x_294 = x_293;
if (lean::is_scalar(x_279)) {
 x_295 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_295 = x_279;
}
lean::cnstr_set(x_295, 0, x_292);
lean::cnstr_set(x_295, 1, x_282);
lean::cnstr_set(x_295, 2, x_284);
lean::cnstr_set(x_295, 3, x_294);
lean::cnstr_set_scalar(x_295, sizeof(void*)*4, x_273);
x_296 = x_295;
return x_296;
}
else
{
obj* x_297; obj* x_299; obj* x_301; obj* x_302; obj* x_304; obj* x_306; obj* x_308; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_297 = lean::cnstr_get(x_186, 1);
x_299 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_301 = x_186;
} else {
 lean::inc(x_297);
 lean::inc(x_299);
 lean::dec(x_186);
 x_301 = lean::box(0);
}
x_302 = lean::cnstr_get(x_190, 0);
x_304 = lean::cnstr_get(x_190, 1);
x_306 = lean::cnstr_get(x_190, 2);
x_308 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_310 = x_190;
} else {
 lean::inc(x_302);
 lean::inc(x_304);
 lean::inc(x_306);
 lean::inc(x_308);
 lean::dec(x_190);
 x_310 = lean::box(0);
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_302);
lean::cnstr_set(x_311, 1, x_304);
lean::cnstr_set(x_311, 2, x_306);
lean::cnstr_set(x_311, 3, x_308);
lean::cnstr_set_scalar(x_311, sizeof(void*)*4, x_273);
x_312 = x_311;
x_313 = 0;
if (lean::is_scalar(x_301)) {
 x_314 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_314 = x_301;
}
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_297);
lean::cnstr_set(x_314, 2, x_299);
lean::cnstr_set(x_314, 3, x_261);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
x_315 = x_314;
if (lean::is_scalar(x_38)) {
 x_316 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_316 = x_38;
}
lean::cnstr_set(x_316, 0, x_315);
lean::cnstr_set(x_316, 1, x_32);
lean::cnstr_set(x_316, 2, x_34);
lean::cnstr_set(x_316, 3, x_36);
lean::cnstr_set_scalar(x_316, sizeof(void*)*4, x_273);
x_317 = x_316;
return x_317;
}
}
}
}
}
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
obj* x_50; 
x_50 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_36, x_1, x_2);
if (lean::obj_tag(x_50) == 0)
{
lean::dec(x_34);
lean::dec(x_38);
lean::dec(x_30);
return x_50;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; 
x_56 = lean::cnstr_get(x_50, 3);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_60; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_68; 
x_58 = lean::cnstr_get(x_50, 1);
x_60 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_62 = x_50;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_50);
 x_62 = lean::box(0);
}
x_63 = 0;
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_56);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_60);
lean::cnstr_set(x_64, 3, x_56);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_63);
x_65 = x_64;
x_66 = 1;
if (lean::is_scalar(x_38)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_38;
}
lean::cnstr_set(x_67, 0, x_30);
lean::cnstr_set(x_67, 1, x_32);
lean::cnstr_set(x_67, 2, x_34);
lean::cnstr_set(x_67, 3, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_66);
x_68 = x_67;
return x_68;
}
else
{
uint8 x_69; 
x_69 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*4);
if (x_69 == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_70 = lean::cnstr_get(x_50, 1);
x_72 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_74 = x_50;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_50);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_56, 0);
x_77 = lean::cnstr_get(x_56, 1);
x_79 = lean::cnstr_get(x_56, 2);
x_81 = lean::cnstr_get(x_56, 3);
if (lean::is_exclusive(x_56)) {
 x_83 = x_56;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_56);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_30);
lean::cnstr_set(x_85, 1, x_32);
lean::cnstr_set(x_85, 2, x_34);
lean::cnstr_set(x_85, 3, x_54);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
if (lean::is_scalar(x_74)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_74;
}
lean::cnstr_set(x_87, 0, x_75);
lean::cnstr_set(x_87, 1, x_77);
lean::cnstr_set(x_87, 2, x_79);
lean::cnstr_set(x_87, 3, x_81);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_84);
x_88 = x_87;
if (lean::is_scalar(x_38)) {
 x_89 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_89 = x_38;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_70);
lean::cnstr_set(x_89, 2, x_72);
lean::cnstr_set(x_89, 3, x_88);
lean::cnstr_set_scalar(x_89, sizeof(void*)*4, x_69);
x_90 = x_89;
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_91 = lean::cnstr_get(x_50, 1);
x_93 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_95 = x_50;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_50);
 x_95 = lean::box(0);
}
x_96 = 0;
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_54);
lean::cnstr_set(x_97, 1, x_91);
lean::cnstr_set(x_97, 2, x_93);
lean::cnstr_set(x_97, 3, x_56);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_96);
x_98 = x_97;
if (lean::is_scalar(x_38)) {
 x_99 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_99 = x_38;
}
lean::cnstr_set(x_99, 0, x_30);
lean::cnstr_set(x_99, 1, x_32);
lean::cnstr_set(x_99, 2, x_34);
lean::cnstr_set(x_99, 3, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_69);
x_100 = x_99;
return x_100;
}
}
}
else
{
uint8 x_101; 
x_101 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_101 == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_102 = lean::cnstr_get(x_50, 1);
x_104 = lean::cnstr_get(x_50, 2);
x_106 = lean::cnstr_get(x_50, 3);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_108 = x_50;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_50);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_54, 0);
x_111 = lean::cnstr_get(x_54, 1);
x_113 = lean::cnstr_get(x_54, 2);
x_115 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_117 = x_54;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_54);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_30);
lean::cnstr_set(x_119, 1, x_32);
lean::cnstr_set(x_119, 2, x_34);
lean::cnstr_set(x_119, 3, x_109);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = x_119;
if (lean::is_scalar(x_108)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_108;
}
lean::cnstr_set(x_121, 0, x_115);
lean::cnstr_set(x_121, 1, x_102);
lean::cnstr_set(x_121, 2, x_104);
lean::cnstr_set(x_121, 3, x_106);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_118);
x_122 = x_121;
if (lean::is_scalar(x_38)) {
 x_123 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_123 = x_38;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_111);
lean::cnstr_set(x_123, 2, x_113);
lean::cnstr_set(x_123, 3, x_122);
lean::cnstr_set_scalar(x_123, sizeof(void*)*4, x_101);
x_124 = x_123;
return x_124;
}
else
{
obj* x_125; 
x_125 = lean::cnstr_get(x_50, 3);
lean::inc(x_125);
if (lean::obj_tag(x_125) == 0)
{
obj* x_127; obj* x_129; obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_127 = lean::cnstr_get(x_50, 1);
x_129 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_131 = x_50;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_50);
 x_131 = lean::box(0);
}
x_132 = 0;
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_54);
lean::cnstr_set(x_133, 1, x_127);
lean::cnstr_set(x_133, 2, x_129);
lean::cnstr_set(x_133, 3, x_125);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_132);
x_134 = x_133;
if (lean::is_scalar(x_38)) {
 x_135 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_135 = x_38;
}
lean::cnstr_set(x_135, 0, x_30);
lean::cnstr_set(x_135, 1, x_32);
lean::cnstr_set(x_135, 2, x_34);
lean::cnstr_set(x_135, 3, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*4, x_101);
x_136 = x_135;
return x_136;
}
else
{
uint8 x_137; 
x_137 = lean::cnstr_get_scalar<uint8>(x_125, sizeof(void*)*4);
if (x_137 == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_38);
x_139 = lean::cnstr_get(x_50, 1);
x_141 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_143 = x_50;
} else {
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_50);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_125, 0);
x_146 = lean::cnstr_get(x_125, 1);
x_148 = lean::cnstr_get(x_125, 2);
x_150 = lean::cnstr_get(x_125, 3);
if (lean::is_exclusive(x_125)) {
 x_152 = x_125;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::inc(x_150);
 lean::dec(x_125);
 x_152 = lean::box(0);
}
lean::inc(x_54);
if (lean::is_scalar(x_152)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_152;
}
lean::cnstr_set(x_154, 0, x_30);
lean::cnstr_set(x_154, 1, x_32);
lean::cnstr_set(x_154, 2, x_34);
lean::cnstr_set(x_154, 3, x_54);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 lean::cnstr_release(x_54, 2);
 lean::cnstr_release(x_54, 3);
 x_155 = x_54;
} else {
 lean::dec(x_54);
 x_155 = lean::box(0);
}
lean::cnstr_set_scalar(x_154, sizeof(void*)*4, x_101);
x_156 = x_154;
if (lean::is_scalar(x_155)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_155;
}
lean::cnstr_set(x_157, 0, x_144);
lean::cnstr_set(x_157, 1, x_146);
lean::cnstr_set(x_157, 2, x_148);
lean::cnstr_set(x_157, 3, x_150);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_101);
x_158 = x_157;
if (lean::is_scalar(x_143)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_143;
}
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_139);
lean::cnstr_set(x_159, 2, x_141);
lean::cnstr_set(x_159, 3, x_158);
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_137);
x_160 = x_159;
return x_160;
}
else
{
obj* x_161; obj* x_163; obj* x_165; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_176; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_161 = lean::cnstr_get(x_50, 1);
x_163 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_165 = x_50;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_50);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_54, 0);
x_168 = lean::cnstr_get(x_54, 1);
x_170 = lean::cnstr_get(x_54, 2);
x_172 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_174 = x_54;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::inc(x_172);
 lean::dec(x_54);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_166);
lean::cnstr_set(x_175, 1, x_168);
lean::cnstr_set(x_175, 2, x_170);
lean::cnstr_set(x_175, 3, x_172);
lean::cnstr_set_scalar(x_175, sizeof(void*)*4, x_137);
x_176 = x_175;
x_177 = 0;
if (lean::is_scalar(x_165)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_165;
}
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_161);
lean::cnstr_set(x_178, 2, x_163);
lean::cnstr_set(x_178, 3, x_125);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_177);
x_179 = x_178;
if (lean::is_scalar(x_38)) {
 x_180 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_180 = x_38;
}
lean::cnstr_set(x_180, 0, x_30);
lean::cnstr_set(x_180, 1, x_32);
lean::cnstr_set(x_180, 2, x_34);
lean::cnstr_set(x_180, 3, x_179);
lean::cnstr_set_scalar(x_180, sizeof(void*)*4, x_137);
x_181 = x_180;
return x_181;
}
}
}
}
}
}
}
}
else
{
uint8 x_182; 
x_182 = l_RBNode_isRed___main___rarg(x_30);
if (x_182 == 0)
{
obj* x_183; obj* x_184; obj* x_185; 
x_183 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_184 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_184 = x_38;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_32);
lean::cnstr_set(x_184, 2, x_34);
lean::cnstr_set(x_184, 3, x_36);
lean::cnstr_set_scalar(x_184, sizeof(void*)*4, x_7);
x_185 = x_184;
return x_185;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_30, x_1, x_2);
if (lean::obj_tag(x_186) == 0)
{
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_38);
return x_186;
}
else
{
obj* x_190; 
x_190 = lean::cnstr_get(x_186, 0);
lean::inc(x_190);
if (lean::obj_tag(x_190) == 0)
{
obj* x_192; 
x_192 = lean::cnstr_get(x_186, 3);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_194; obj* x_196; obj* x_198; uint8 x_199; obj* x_200; obj* x_201; uint8 x_202; obj* x_203; obj* x_204; 
x_194 = lean::cnstr_get(x_186, 1);
x_196 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_198 = x_186;
} else {
 lean::inc(x_194);
 lean::inc(x_196);
 lean::dec(x_186);
 x_198 = lean::box(0);
}
x_199 = 0;
if (lean::is_scalar(x_198)) {
 x_200 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_200 = x_198;
}
lean::cnstr_set(x_200, 0, x_192);
lean::cnstr_set(x_200, 1, x_194);
lean::cnstr_set(x_200, 2, x_196);
lean::cnstr_set(x_200, 3, x_192);
lean::cnstr_set_scalar(x_200, sizeof(void*)*4, x_199);
x_201 = x_200;
x_202 = 1;
if (lean::is_scalar(x_38)) {
 x_203 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_203 = x_38;
}
lean::cnstr_set(x_203, 0, x_201);
lean::cnstr_set(x_203, 1, x_32);
lean::cnstr_set(x_203, 2, x_34);
lean::cnstr_set(x_203, 3, x_36);
lean::cnstr_set_scalar(x_203, sizeof(void*)*4, x_202);
x_204 = x_203;
return x_204;
}
else
{
uint8 x_205; 
x_205 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*4);
if (x_205 == 0)
{
obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_206 = lean::cnstr_get(x_186, 1);
x_208 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_210 = x_186;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_186);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_192, 0);
x_213 = lean::cnstr_get(x_192, 1);
x_215 = lean::cnstr_get(x_192, 2);
x_217 = lean::cnstr_get(x_192, 3);
if (lean::is_exclusive(x_192)) {
 x_219 = x_192;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::inc(x_215);
 lean::inc(x_217);
 lean::dec(x_192);
 x_219 = lean::box(0);
}
x_220 = 1;
if (lean::is_scalar(x_219)) {
 x_221 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_221 = x_219;
}
lean::cnstr_set(x_221, 0, x_190);
lean::cnstr_set(x_221, 1, x_206);
lean::cnstr_set(x_221, 2, x_208);
lean::cnstr_set(x_221, 3, x_211);
lean::cnstr_set_scalar(x_221, sizeof(void*)*4, x_220);
x_222 = x_221;
if (lean::is_scalar(x_210)) {
 x_223 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_223 = x_210;
}
lean::cnstr_set(x_223, 0, x_217);
lean::cnstr_set(x_223, 1, x_32);
lean::cnstr_set(x_223, 2, x_34);
lean::cnstr_set(x_223, 3, x_36);
lean::cnstr_set_scalar(x_223, sizeof(void*)*4, x_220);
x_224 = x_223;
if (lean::is_scalar(x_38)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_38;
}
lean::cnstr_set(x_225, 0, x_222);
lean::cnstr_set(x_225, 1, x_213);
lean::cnstr_set(x_225, 2, x_215);
lean::cnstr_set(x_225, 3, x_224);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_205);
x_226 = x_225;
return x_226;
}
else
{
obj* x_227; obj* x_229; obj* x_231; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_227 = lean::cnstr_get(x_186, 1);
x_229 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_231 = x_186;
} else {
 lean::inc(x_227);
 lean::inc(x_229);
 lean::dec(x_186);
 x_231 = lean::box(0);
}
x_232 = 0;
if (lean::is_scalar(x_231)) {
 x_233 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_233 = x_231;
}
lean::cnstr_set(x_233, 0, x_190);
lean::cnstr_set(x_233, 1, x_227);
lean::cnstr_set(x_233, 2, x_229);
lean::cnstr_set(x_233, 3, x_192);
lean::cnstr_set_scalar(x_233, sizeof(void*)*4, x_232);
x_234 = x_233;
if (lean::is_scalar(x_38)) {
 x_235 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_235 = x_38;
}
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set(x_235, 1, x_32);
lean::cnstr_set(x_235, 2, x_34);
lean::cnstr_set(x_235, 3, x_36);
lean::cnstr_set_scalar(x_235, sizeof(void*)*4, x_205);
x_236 = x_235;
return x_236;
}
}
}
else
{
uint8 x_237; 
x_237 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*4);
if (x_237 == 0)
{
obj* x_238; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_251; obj* x_253; uint8 x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_238 = lean::cnstr_get(x_186, 1);
x_240 = lean::cnstr_get(x_186, 2);
x_242 = lean::cnstr_get(x_186, 3);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 x_244 = x_186;
} else {
 lean::inc(x_238);
 lean::inc(x_240);
 lean::inc(x_242);
 lean::dec(x_186);
 x_244 = lean::box(0);
}
x_245 = lean::cnstr_get(x_190, 0);
x_247 = lean::cnstr_get(x_190, 1);
x_249 = lean::cnstr_get(x_190, 2);
x_251 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_253 = x_190;
} else {
 lean::inc(x_245);
 lean::inc(x_247);
 lean::inc(x_249);
 lean::inc(x_251);
 lean::dec(x_190);
 x_253 = lean::box(0);
}
x_254 = 1;
if (lean::is_scalar(x_253)) {
 x_255 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_255 = x_253;
}
lean::cnstr_set(x_255, 0, x_245);
lean::cnstr_set(x_255, 1, x_247);
lean::cnstr_set(x_255, 2, x_249);
lean::cnstr_set(x_255, 3, x_251);
lean::cnstr_set_scalar(x_255, sizeof(void*)*4, x_254);
x_256 = x_255;
if (lean::is_scalar(x_244)) {
 x_257 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_257 = x_244;
}
lean::cnstr_set(x_257, 0, x_242);
lean::cnstr_set(x_257, 1, x_32);
lean::cnstr_set(x_257, 2, x_34);
lean::cnstr_set(x_257, 3, x_36);
lean::cnstr_set_scalar(x_257, sizeof(void*)*4, x_254);
x_258 = x_257;
if (lean::is_scalar(x_38)) {
 x_259 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_259 = x_38;
}
lean::cnstr_set(x_259, 0, x_256);
lean::cnstr_set(x_259, 1, x_238);
lean::cnstr_set(x_259, 2, x_240);
lean::cnstr_set(x_259, 3, x_258);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_237);
x_260 = x_259;
return x_260;
}
else
{
obj* x_261; 
x_261 = lean::cnstr_get(x_186, 3);
lean::inc(x_261);
if (lean::obj_tag(x_261) == 0)
{
obj* x_263; obj* x_265; obj* x_267; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_263 = lean::cnstr_get(x_186, 1);
x_265 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_267 = x_186;
} else {
 lean::inc(x_263);
 lean::inc(x_265);
 lean::dec(x_186);
 x_267 = lean::box(0);
}
x_268 = 0;
if (lean::is_scalar(x_267)) {
 x_269 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_269 = x_267;
}
lean::cnstr_set(x_269, 0, x_190);
lean::cnstr_set(x_269, 1, x_263);
lean::cnstr_set(x_269, 2, x_265);
lean::cnstr_set(x_269, 3, x_261);
lean::cnstr_set_scalar(x_269, sizeof(void*)*4, x_268);
x_270 = x_269;
if (lean::is_scalar(x_38)) {
 x_271 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_271 = x_38;
}
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_32);
lean::cnstr_set(x_271, 2, x_34);
lean::cnstr_set(x_271, 3, x_36);
lean::cnstr_set_scalar(x_271, sizeof(void*)*4, x_237);
x_272 = x_271;
return x_272;
}
else
{
uint8 x_273; 
x_273 = lean::cnstr_get_scalar<uint8>(x_261, sizeof(void*)*4);
if (x_273 == 0)
{
obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_286; obj* x_288; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_38);
x_275 = lean::cnstr_get(x_186, 1);
x_277 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_279 = x_186;
} else {
 lean::inc(x_275);
 lean::inc(x_277);
 lean::dec(x_186);
 x_279 = lean::box(0);
}
x_280 = lean::cnstr_get(x_261, 0);
x_282 = lean::cnstr_get(x_261, 1);
x_284 = lean::cnstr_get(x_261, 2);
x_286 = lean::cnstr_get(x_261, 3);
if (lean::is_exclusive(x_261)) {
 x_288 = x_261;
} else {
 lean::inc(x_280);
 lean::inc(x_282);
 lean::inc(x_284);
 lean::inc(x_286);
 lean::dec(x_261);
 x_288 = lean::box(0);
}
lean::inc(x_190);
if (lean::is_scalar(x_288)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_288;
}
lean::cnstr_set(x_290, 0, x_190);
lean::cnstr_set(x_290, 1, x_275);
lean::cnstr_set(x_290, 2, x_277);
lean::cnstr_set(x_290, 3, x_280);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 lean::cnstr_release(x_190, 2);
 lean::cnstr_release(x_190, 3);
 x_291 = x_190;
} else {
 lean::dec(x_190);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_237);
x_292 = x_290;
if (lean::is_scalar(x_291)) {
 x_293 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_293 = x_291;
}
lean::cnstr_set(x_293, 0, x_286);
lean::cnstr_set(x_293, 1, x_32);
lean::cnstr_set(x_293, 2, x_34);
lean::cnstr_set(x_293, 3, x_36);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_237);
x_294 = x_293;
if (lean::is_scalar(x_279)) {
 x_295 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_295 = x_279;
}
lean::cnstr_set(x_295, 0, x_292);
lean::cnstr_set(x_295, 1, x_282);
lean::cnstr_set(x_295, 2, x_284);
lean::cnstr_set(x_295, 3, x_294);
lean::cnstr_set_scalar(x_295, sizeof(void*)*4, x_273);
x_296 = x_295;
return x_296;
}
else
{
obj* x_297; obj* x_299; obj* x_301; obj* x_302; obj* x_304; obj* x_306; obj* x_308; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_297 = lean::cnstr_get(x_186, 1);
x_299 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_301 = x_186;
} else {
 lean::inc(x_297);
 lean::inc(x_299);
 lean::dec(x_186);
 x_301 = lean::box(0);
}
x_302 = lean::cnstr_get(x_190, 0);
x_304 = lean::cnstr_get(x_190, 1);
x_306 = lean::cnstr_get(x_190, 2);
x_308 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_310 = x_190;
} else {
 lean::inc(x_302);
 lean::inc(x_304);
 lean::inc(x_306);
 lean::inc(x_308);
 lean::dec(x_190);
 x_310 = lean::box(0);
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_302);
lean::cnstr_set(x_311, 1, x_304);
lean::cnstr_set(x_311, 2, x_306);
lean::cnstr_set(x_311, 3, x_308);
lean::cnstr_set_scalar(x_311, sizeof(void*)*4, x_273);
x_312 = x_311;
x_313 = 0;
if (lean::is_scalar(x_301)) {
 x_314 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_314 = x_301;
}
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_297);
lean::cnstr_set(x_314, 2, x_299);
lean::cnstr_set(x_314, 3, x_261);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
x_315 = x_314;
if (lean::is_scalar(x_38)) {
 x_316 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_316 = x_38;
}
lean::cnstr_set(x_316, 0, x_315);
lean::cnstr_set(x_316, 1, x_32);
lean::cnstr_set(x_316, 2, x_34);
lean::cnstr_set(x_316, 3, x_36);
lean::cnstr_set_scalar(x_316, sizeof(void*)*4, x_273);
x_317 = x_316;
return x_317;
}
}
}
}
}
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
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(obj* x_0, uint32 x_1, obj* x_2) {
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
x_24 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_14, x_1, x_2);
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
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_8, x_1, x_2);
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
x_47 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_36, x_1, x_2);
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
obj* x_50; 
x_50 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_36, x_1, x_2);
if (lean::obj_tag(x_50) == 0)
{
lean::dec(x_34);
lean::dec(x_38);
lean::dec(x_30);
return x_50;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; 
x_56 = lean::cnstr_get(x_50, 3);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_58; obj* x_60; obj* x_62; uint8 x_63; obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_68; 
x_58 = lean::cnstr_get(x_50, 1);
x_60 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_62 = x_50;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::dec(x_50);
 x_62 = lean::box(0);
}
x_63 = 0;
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_56);
lean::cnstr_set(x_64, 1, x_58);
lean::cnstr_set(x_64, 2, x_60);
lean::cnstr_set(x_64, 3, x_56);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_63);
x_65 = x_64;
x_66 = 1;
if (lean::is_scalar(x_38)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_38;
}
lean::cnstr_set(x_67, 0, x_30);
lean::cnstr_set(x_67, 1, x_32);
lean::cnstr_set(x_67, 2, x_34);
lean::cnstr_set(x_67, 3, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_66);
x_68 = x_67;
return x_68;
}
else
{
uint8 x_69; 
x_69 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*4);
if (x_69 == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_70 = lean::cnstr_get(x_50, 1);
x_72 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_74 = x_50;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_50);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_56, 0);
x_77 = lean::cnstr_get(x_56, 1);
x_79 = lean::cnstr_get(x_56, 2);
x_81 = lean::cnstr_get(x_56, 3);
if (lean::is_exclusive(x_56)) {
 x_83 = x_56;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_56);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_30);
lean::cnstr_set(x_85, 1, x_32);
lean::cnstr_set(x_85, 2, x_34);
lean::cnstr_set(x_85, 3, x_54);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
if (lean::is_scalar(x_74)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_74;
}
lean::cnstr_set(x_87, 0, x_75);
lean::cnstr_set(x_87, 1, x_77);
lean::cnstr_set(x_87, 2, x_79);
lean::cnstr_set(x_87, 3, x_81);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_84);
x_88 = x_87;
if (lean::is_scalar(x_38)) {
 x_89 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_89 = x_38;
}
lean::cnstr_set(x_89, 0, x_86);
lean::cnstr_set(x_89, 1, x_70);
lean::cnstr_set(x_89, 2, x_72);
lean::cnstr_set(x_89, 3, x_88);
lean::cnstr_set_scalar(x_89, sizeof(void*)*4, x_69);
x_90 = x_89;
return x_90;
}
else
{
obj* x_91; obj* x_93; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_91 = lean::cnstr_get(x_50, 1);
x_93 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_95 = x_50;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_50);
 x_95 = lean::box(0);
}
x_96 = 0;
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_54);
lean::cnstr_set(x_97, 1, x_91);
lean::cnstr_set(x_97, 2, x_93);
lean::cnstr_set(x_97, 3, x_56);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_96);
x_98 = x_97;
if (lean::is_scalar(x_38)) {
 x_99 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_99 = x_38;
}
lean::cnstr_set(x_99, 0, x_30);
lean::cnstr_set(x_99, 1, x_32);
lean::cnstr_set(x_99, 2, x_34);
lean::cnstr_set(x_99, 3, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*4, x_69);
x_100 = x_99;
return x_100;
}
}
}
else
{
uint8 x_101; 
x_101 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_101 == 0)
{
obj* x_102; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_102 = lean::cnstr_get(x_50, 1);
x_104 = lean::cnstr_get(x_50, 2);
x_106 = lean::cnstr_get(x_50, 3);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_108 = x_50;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_50);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_54, 0);
x_111 = lean::cnstr_get(x_54, 1);
x_113 = lean::cnstr_get(x_54, 2);
x_115 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_117 = x_54;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_54);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_30);
lean::cnstr_set(x_119, 1, x_32);
lean::cnstr_set(x_119, 2, x_34);
lean::cnstr_set(x_119, 3, x_109);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = x_119;
if (lean::is_scalar(x_108)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_108;
}
lean::cnstr_set(x_121, 0, x_115);
lean::cnstr_set(x_121, 1, x_102);
lean::cnstr_set(x_121, 2, x_104);
lean::cnstr_set(x_121, 3, x_106);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_118);
x_122 = x_121;
if (lean::is_scalar(x_38)) {
 x_123 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_123 = x_38;
}
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_111);
lean::cnstr_set(x_123, 2, x_113);
lean::cnstr_set(x_123, 3, x_122);
lean::cnstr_set_scalar(x_123, sizeof(void*)*4, x_101);
x_124 = x_123;
return x_124;
}
else
{
obj* x_125; 
x_125 = lean::cnstr_get(x_50, 3);
lean::inc(x_125);
if (lean::obj_tag(x_125) == 0)
{
obj* x_127; obj* x_129; obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_127 = lean::cnstr_get(x_50, 1);
x_129 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_131 = x_50;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_50);
 x_131 = lean::box(0);
}
x_132 = 0;
if (lean::is_scalar(x_131)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_131;
}
lean::cnstr_set(x_133, 0, x_54);
lean::cnstr_set(x_133, 1, x_127);
lean::cnstr_set(x_133, 2, x_129);
lean::cnstr_set(x_133, 3, x_125);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_132);
x_134 = x_133;
if (lean::is_scalar(x_38)) {
 x_135 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_135 = x_38;
}
lean::cnstr_set(x_135, 0, x_30);
lean::cnstr_set(x_135, 1, x_32);
lean::cnstr_set(x_135, 2, x_34);
lean::cnstr_set(x_135, 3, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*4, x_101);
x_136 = x_135;
return x_136;
}
else
{
uint8 x_137; 
x_137 = lean::cnstr_get_scalar<uint8>(x_125, sizeof(void*)*4);
if (x_137 == 0)
{
obj* x_139; obj* x_141; obj* x_143; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_38);
x_139 = lean::cnstr_get(x_50, 1);
x_141 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_143 = x_50;
} else {
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_50);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_125, 0);
x_146 = lean::cnstr_get(x_125, 1);
x_148 = lean::cnstr_get(x_125, 2);
x_150 = lean::cnstr_get(x_125, 3);
if (lean::is_exclusive(x_125)) {
 x_152 = x_125;
} else {
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::inc(x_150);
 lean::dec(x_125);
 x_152 = lean::box(0);
}
lean::inc(x_54);
if (lean::is_scalar(x_152)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_152;
}
lean::cnstr_set(x_154, 0, x_30);
lean::cnstr_set(x_154, 1, x_32);
lean::cnstr_set(x_154, 2, x_34);
lean::cnstr_set(x_154, 3, x_54);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 lean::cnstr_release(x_54, 2);
 lean::cnstr_release(x_54, 3);
 x_155 = x_54;
} else {
 lean::dec(x_54);
 x_155 = lean::box(0);
}
lean::cnstr_set_scalar(x_154, sizeof(void*)*4, x_101);
x_156 = x_154;
if (lean::is_scalar(x_155)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_155;
}
lean::cnstr_set(x_157, 0, x_144);
lean::cnstr_set(x_157, 1, x_146);
lean::cnstr_set(x_157, 2, x_148);
lean::cnstr_set(x_157, 3, x_150);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_101);
x_158 = x_157;
if (lean::is_scalar(x_143)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_143;
}
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_139);
lean::cnstr_set(x_159, 2, x_141);
lean::cnstr_set(x_159, 3, x_158);
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_137);
x_160 = x_159;
return x_160;
}
else
{
obj* x_161; obj* x_163; obj* x_165; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_174; obj* x_175; obj* x_176; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
x_161 = lean::cnstr_get(x_50, 1);
x_163 = lean::cnstr_get(x_50, 2);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 lean::cnstr_release(x_50, 3);
 x_165 = x_50;
} else {
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_50);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_54, 0);
x_168 = lean::cnstr_get(x_54, 1);
x_170 = lean::cnstr_get(x_54, 2);
x_172 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_174 = x_54;
} else {
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::inc(x_172);
 lean::dec(x_54);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_166);
lean::cnstr_set(x_175, 1, x_168);
lean::cnstr_set(x_175, 2, x_170);
lean::cnstr_set(x_175, 3, x_172);
lean::cnstr_set_scalar(x_175, sizeof(void*)*4, x_137);
x_176 = x_175;
x_177 = 0;
if (lean::is_scalar(x_165)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_165;
}
lean::cnstr_set(x_178, 0, x_176);
lean::cnstr_set(x_178, 1, x_161);
lean::cnstr_set(x_178, 2, x_163);
lean::cnstr_set(x_178, 3, x_125);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_177);
x_179 = x_178;
if (lean::is_scalar(x_38)) {
 x_180 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_180 = x_38;
}
lean::cnstr_set(x_180, 0, x_30);
lean::cnstr_set(x_180, 1, x_32);
lean::cnstr_set(x_180, 2, x_34);
lean::cnstr_set(x_180, 3, x_179);
lean::cnstr_set_scalar(x_180, sizeof(void*)*4, x_137);
x_181 = x_180;
return x_181;
}
}
}
}
}
}
}
}
else
{
uint8 x_182; 
x_182 = l_RBNode_isRed___main___rarg(x_30);
if (x_182 == 0)
{
obj* x_183; obj* x_184; obj* x_185; 
x_183 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_184 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_184 = x_38;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_32);
lean::cnstr_set(x_184, 2, x_34);
lean::cnstr_set(x_184, 3, x_36);
lean::cnstr_set_scalar(x_184, sizeof(void*)*4, x_7);
x_185 = x_184;
return x_185;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_30, x_1, x_2);
if (lean::obj_tag(x_186) == 0)
{
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_38);
return x_186;
}
else
{
obj* x_190; 
x_190 = lean::cnstr_get(x_186, 0);
lean::inc(x_190);
if (lean::obj_tag(x_190) == 0)
{
obj* x_192; 
x_192 = lean::cnstr_get(x_186, 3);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_194; obj* x_196; obj* x_198; uint8 x_199; obj* x_200; obj* x_201; uint8 x_202; obj* x_203; obj* x_204; 
x_194 = lean::cnstr_get(x_186, 1);
x_196 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_198 = x_186;
} else {
 lean::inc(x_194);
 lean::inc(x_196);
 lean::dec(x_186);
 x_198 = lean::box(0);
}
x_199 = 0;
if (lean::is_scalar(x_198)) {
 x_200 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_200 = x_198;
}
lean::cnstr_set(x_200, 0, x_192);
lean::cnstr_set(x_200, 1, x_194);
lean::cnstr_set(x_200, 2, x_196);
lean::cnstr_set(x_200, 3, x_192);
lean::cnstr_set_scalar(x_200, sizeof(void*)*4, x_199);
x_201 = x_200;
x_202 = 1;
if (lean::is_scalar(x_38)) {
 x_203 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_203 = x_38;
}
lean::cnstr_set(x_203, 0, x_201);
lean::cnstr_set(x_203, 1, x_32);
lean::cnstr_set(x_203, 2, x_34);
lean::cnstr_set(x_203, 3, x_36);
lean::cnstr_set_scalar(x_203, sizeof(void*)*4, x_202);
x_204 = x_203;
return x_204;
}
else
{
uint8 x_205; 
x_205 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*4);
if (x_205 == 0)
{
obj* x_206; obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_219; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_206 = lean::cnstr_get(x_186, 1);
x_208 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_210 = x_186;
} else {
 lean::inc(x_206);
 lean::inc(x_208);
 lean::dec(x_186);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_192, 0);
x_213 = lean::cnstr_get(x_192, 1);
x_215 = lean::cnstr_get(x_192, 2);
x_217 = lean::cnstr_get(x_192, 3);
if (lean::is_exclusive(x_192)) {
 x_219 = x_192;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::inc(x_215);
 lean::inc(x_217);
 lean::dec(x_192);
 x_219 = lean::box(0);
}
x_220 = 1;
if (lean::is_scalar(x_219)) {
 x_221 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_221 = x_219;
}
lean::cnstr_set(x_221, 0, x_190);
lean::cnstr_set(x_221, 1, x_206);
lean::cnstr_set(x_221, 2, x_208);
lean::cnstr_set(x_221, 3, x_211);
lean::cnstr_set_scalar(x_221, sizeof(void*)*4, x_220);
x_222 = x_221;
if (lean::is_scalar(x_210)) {
 x_223 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_223 = x_210;
}
lean::cnstr_set(x_223, 0, x_217);
lean::cnstr_set(x_223, 1, x_32);
lean::cnstr_set(x_223, 2, x_34);
lean::cnstr_set(x_223, 3, x_36);
lean::cnstr_set_scalar(x_223, sizeof(void*)*4, x_220);
x_224 = x_223;
if (lean::is_scalar(x_38)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_38;
}
lean::cnstr_set(x_225, 0, x_222);
lean::cnstr_set(x_225, 1, x_213);
lean::cnstr_set(x_225, 2, x_215);
lean::cnstr_set(x_225, 3, x_224);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_205);
x_226 = x_225;
return x_226;
}
else
{
obj* x_227; obj* x_229; obj* x_231; uint8 x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_227 = lean::cnstr_get(x_186, 1);
x_229 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_231 = x_186;
} else {
 lean::inc(x_227);
 lean::inc(x_229);
 lean::dec(x_186);
 x_231 = lean::box(0);
}
x_232 = 0;
if (lean::is_scalar(x_231)) {
 x_233 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_233 = x_231;
}
lean::cnstr_set(x_233, 0, x_190);
lean::cnstr_set(x_233, 1, x_227);
lean::cnstr_set(x_233, 2, x_229);
lean::cnstr_set(x_233, 3, x_192);
lean::cnstr_set_scalar(x_233, sizeof(void*)*4, x_232);
x_234 = x_233;
if (lean::is_scalar(x_38)) {
 x_235 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_235 = x_38;
}
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set(x_235, 1, x_32);
lean::cnstr_set(x_235, 2, x_34);
lean::cnstr_set(x_235, 3, x_36);
lean::cnstr_set_scalar(x_235, sizeof(void*)*4, x_205);
x_236 = x_235;
return x_236;
}
}
}
else
{
uint8 x_237; 
x_237 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*4);
if (x_237 == 0)
{
obj* x_238; obj* x_240; obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_249; obj* x_251; obj* x_253; uint8 x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
x_238 = lean::cnstr_get(x_186, 1);
x_240 = lean::cnstr_get(x_186, 2);
x_242 = lean::cnstr_get(x_186, 3);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 x_244 = x_186;
} else {
 lean::inc(x_238);
 lean::inc(x_240);
 lean::inc(x_242);
 lean::dec(x_186);
 x_244 = lean::box(0);
}
x_245 = lean::cnstr_get(x_190, 0);
x_247 = lean::cnstr_get(x_190, 1);
x_249 = lean::cnstr_get(x_190, 2);
x_251 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_253 = x_190;
} else {
 lean::inc(x_245);
 lean::inc(x_247);
 lean::inc(x_249);
 lean::inc(x_251);
 lean::dec(x_190);
 x_253 = lean::box(0);
}
x_254 = 1;
if (lean::is_scalar(x_253)) {
 x_255 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_255 = x_253;
}
lean::cnstr_set(x_255, 0, x_245);
lean::cnstr_set(x_255, 1, x_247);
lean::cnstr_set(x_255, 2, x_249);
lean::cnstr_set(x_255, 3, x_251);
lean::cnstr_set_scalar(x_255, sizeof(void*)*4, x_254);
x_256 = x_255;
if (lean::is_scalar(x_244)) {
 x_257 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_257 = x_244;
}
lean::cnstr_set(x_257, 0, x_242);
lean::cnstr_set(x_257, 1, x_32);
lean::cnstr_set(x_257, 2, x_34);
lean::cnstr_set(x_257, 3, x_36);
lean::cnstr_set_scalar(x_257, sizeof(void*)*4, x_254);
x_258 = x_257;
if (lean::is_scalar(x_38)) {
 x_259 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_259 = x_38;
}
lean::cnstr_set(x_259, 0, x_256);
lean::cnstr_set(x_259, 1, x_238);
lean::cnstr_set(x_259, 2, x_240);
lean::cnstr_set(x_259, 3, x_258);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_237);
x_260 = x_259;
return x_260;
}
else
{
obj* x_261; 
x_261 = lean::cnstr_get(x_186, 3);
lean::inc(x_261);
if (lean::obj_tag(x_261) == 0)
{
obj* x_263; obj* x_265; obj* x_267; uint8 x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; 
x_263 = lean::cnstr_get(x_186, 1);
x_265 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_267 = x_186;
} else {
 lean::inc(x_263);
 lean::inc(x_265);
 lean::dec(x_186);
 x_267 = lean::box(0);
}
x_268 = 0;
if (lean::is_scalar(x_267)) {
 x_269 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_269 = x_267;
}
lean::cnstr_set(x_269, 0, x_190);
lean::cnstr_set(x_269, 1, x_263);
lean::cnstr_set(x_269, 2, x_265);
lean::cnstr_set(x_269, 3, x_261);
lean::cnstr_set_scalar(x_269, sizeof(void*)*4, x_268);
x_270 = x_269;
if (lean::is_scalar(x_38)) {
 x_271 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_271 = x_38;
}
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_32);
lean::cnstr_set(x_271, 2, x_34);
lean::cnstr_set(x_271, 3, x_36);
lean::cnstr_set_scalar(x_271, sizeof(void*)*4, x_237);
x_272 = x_271;
return x_272;
}
else
{
uint8 x_273; 
x_273 = lean::cnstr_get_scalar<uint8>(x_261, sizeof(void*)*4);
if (x_273 == 0)
{
obj* x_275; obj* x_277; obj* x_279; obj* x_280; obj* x_282; obj* x_284; obj* x_286; obj* x_288; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_38);
x_275 = lean::cnstr_get(x_186, 1);
x_277 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_279 = x_186;
} else {
 lean::inc(x_275);
 lean::inc(x_277);
 lean::dec(x_186);
 x_279 = lean::box(0);
}
x_280 = lean::cnstr_get(x_261, 0);
x_282 = lean::cnstr_get(x_261, 1);
x_284 = lean::cnstr_get(x_261, 2);
x_286 = lean::cnstr_get(x_261, 3);
if (lean::is_exclusive(x_261)) {
 x_288 = x_261;
} else {
 lean::inc(x_280);
 lean::inc(x_282);
 lean::inc(x_284);
 lean::inc(x_286);
 lean::dec(x_261);
 x_288 = lean::box(0);
}
lean::inc(x_190);
if (lean::is_scalar(x_288)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_288;
}
lean::cnstr_set(x_290, 0, x_190);
lean::cnstr_set(x_290, 1, x_275);
lean::cnstr_set(x_290, 2, x_277);
lean::cnstr_set(x_290, 3, x_280);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 lean::cnstr_release(x_190, 2);
 lean::cnstr_release(x_190, 3);
 x_291 = x_190;
} else {
 lean::dec(x_190);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_237);
x_292 = x_290;
if (lean::is_scalar(x_291)) {
 x_293 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_293 = x_291;
}
lean::cnstr_set(x_293, 0, x_286);
lean::cnstr_set(x_293, 1, x_32);
lean::cnstr_set(x_293, 2, x_34);
lean::cnstr_set(x_293, 3, x_36);
lean::cnstr_set_scalar(x_293, sizeof(void*)*4, x_237);
x_294 = x_293;
if (lean::is_scalar(x_279)) {
 x_295 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_295 = x_279;
}
lean::cnstr_set(x_295, 0, x_292);
lean::cnstr_set(x_295, 1, x_282);
lean::cnstr_set(x_295, 2, x_284);
lean::cnstr_set(x_295, 3, x_294);
lean::cnstr_set_scalar(x_295, sizeof(void*)*4, x_273);
x_296 = x_295;
return x_296;
}
else
{
obj* x_297; obj* x_299; obj* x_301; obj* x_302; obj* x_304; obj* x_306; obj* x_308; obj* x_310; obj* x_311; obj* x_312; uint8 x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; 
x_297 = lean::cnstr_get(x_186, 1);
x_299 = lean::cnstr_get(x_186, 2);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_release(x_186, 3);
 x_301 = x_186;
} else {
 lean::inc(x_297);
 lean::inc(x_299);
 lean::dec(x_186);
 x_301 = lean::box(0);
}
x_302 = lean::cnstr_get(x_190, 0);
x_304 = lean::cnstr_get(x_190, 1);
x_306 = lean::cnstr_get(x_190, 2);
x_308 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_310 = x_190;
} else {
 lean::inc(x_302);
 lean::inc(x_304);
 lean::inc(x_306);
 lean::inc(x_308);
 lean::dec(x_190);
 x_310 = lean::box(0);
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_302);
lean::cnstr_set(x_311, 1, x_304);
lean::cnstr_set(x_311, 2, x_306);
lean::cnstr_set(x_311, 3, x_308);
lean::cnstr_set_scalar(x_311, sizeof(void*)*4, x_273);
x_312 = x_311;
x_313 = 0;
if (lean::is_scalar(x_301)) {
 x_314 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_314 = x_301;
}
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_297);
lean::cnstr_set(x_314, 2, x_299);
lean::cnstr_set(x_314, 3, x_261);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_313);
x_315 = x_314;
if (lean::is_scalar(x_38)) {
 x_316 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_316 = x_38;
}
lean::cnstr_set(x_316, 0, x_315);
lean::cnstr_set(x_316, 1, x_32);
lean::cnstr_set(x_316, 2, x_34);
lean::cnstr_set(x_316, 3, x_36);
lean::cnstr_set_scalar(x_316, sizeof(void*)*4, x_273);
x_317 = x_316;
return x_317;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed), 3, 0);
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
uint32 x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_10 = lean::string_utf8_get(x_0, x_3);
x_11 = lean::string_utf8_next(x_0, x_3);
lean::inc(x_6);
x_13 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_6, x_10);
x_14 = l_RBNode_isRed___main___rarg(x_6);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; 
x_15 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_0, x_1, x_11);
lean::dec(x_11);
if (x_14 == 0)
{
obj* x_17; obj* x_18; 
x_17 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_6, x_10, x_15);
if (lean::is_scalar(x_8)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_8;
}
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_6, x_10, x_15);
x_20 = l_RBNode_setBlack___main___rarg(x_19);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
else
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
lean::dec(x_13);
x_25 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_0, x_1, x_22, x_11);
lean::dec(x_11);
if (x_14 == 0)
{
obj* x_27; obj* x_28; 
x_27 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_6, x_10, x_25);
if (lean::is_scalar(x_8)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_8;
}
lean::cnstr_set(x_28, 0, x_4);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_6, x_10, x_25);
x_30 = l_RBNode_setBlack___main___rarg(x_29);
if (lean::is_scalar(x_8)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_8;
}
lean::cnstr_set(x_31, 0, x_4);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_4);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_1);
if (lean::is_scalar(x_8)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_8;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_6);
return x_34;
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
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(x_0);
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
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(x_0);
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg___boxed), 2, 0);
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
uint32 x_10; obj* x_11; obj* x_13; 
lean::dec(x_3);
x_10 = lean::string_utf8_get(x_0, x_2);
x_11 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_13 = l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(x_5, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; 
lean::dec(x_11);
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_1 = x_16;
x_2 = x_11;
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(x_0, x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1(x_0);
lean::dec(x_0);
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg___boxed), 2, 0);
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
obj* x_11; uint32 x_13; obj* x_14; obj* x_16; 
lean::inc(x_2);
x_11 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_4, x_2, x_3);
lean::dec(x_3);
x_13 = lean::string_utf8_get(x_0, x_2);
x_14 = lean::string_utf8_next(x_0, x_2);
lean::dec(x_2);
x_16 = l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(x_6, x_13);
if (lean::obj_tag(x_16) == 0)
{
lean::dec(x_14);
return x_11;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_1 = x_18;
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
else
{
obj* x_23; 
lean::dec(x_6);
x_23 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_4, x_2, x_3);
lean::dec(x_3);
return x_23;
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(x_0, x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1(x_0);
lean::dec(x_0);
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg(obj* x_0, uint32 x_1) {
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg___boxed), 2, 0);
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
obj* x_6; obj* x_7; obj* x_9; obj* x_11; uint32 x_14; obj* x_15; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
x_14 = l_String_OldIterator_curr___main(x_2);
x_15 = l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg(x_11, x_14);
if (lean::obj_tag(x_9) == 0)
{
if (lean::obj_tag(x_15) == 0)
{
lean::dec(x_7);
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
x_0 = x_7;
x_1 = x_18;
x_2 = x_21;
goto _start;
}
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_3);
x_24 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_26 = x_9;
} else {
 lean::inc(x_24);
 lean::dec(x_9);
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
lean::dec(x_7);
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
x_0 = x_7;
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
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___rarg(x_0, x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main___at___private_init_lean_parser_trie_6__oldMatchPrefixAux___main___spec__1(x_0);
lean::dec(x_0);
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
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint32 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::cnstr_get(x_1, 3);
x_6 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg(x_0, x_2);
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
x_0 = x_21;
x_1 = x_5;
goto _start;
}
}
}
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_trie_7__toStringAux___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::box(0);
x_3 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg(x_2, x_1);
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
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_fold___main___at___private_init_lean_parser_trie_7__toStringAux___main___spec__2(x_0);
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
if (io_result_is_error(w)) return w;
 l_Lean_Parser_Trie_empty___closed__1 = _init_l_Lean_Parser_Trie_empty___closed__1();
lean::mark_persistent(l_Lean_Parser_Trie_empty___closed__1);
 l_Lean_Parser_Trie_HasEmptyc___closed__1 = _init_l_Lean_Parser_Trie_HasEmptyc___closed__1();
lean::mark_persistent(l_Lean_Parser_Trie_HasEmptyc___closed__1);
return w;
}

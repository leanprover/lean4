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
obj* l___private_init_lean_parser_trie_6__toStringAux___rarg(obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2(obj*);
obj* l___private_init_lean_parser_trie_6__toStringAux(obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_Trie_find(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(obj*, uint32);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4(obj*);
extern obj* l_Lean_Options_empty;
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(obj*, uint32, obj*);
obj* l_Lean_Parser_Trie_insert___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_Inhabited(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_4__updtAcc(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1(obj*);
obj* l___private_init_lean_parser_trie_3__findAux(obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
uint8 l_RBNode_isRed___rarg(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3(obj*);
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2___rarg(obj*, obj*);
obj* l_Lean_Parser_Trie_HasEmptyc(obj*);
obj* l_Lean_Parser_Trie_HasToString___rarg(obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l___private_init_lean_parser_trie_2__insertAux___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main(obj*);
obj* l_Char_quoteCore(uint32);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(obj*, obj*, obj*);
uint8 l_UInt32_decLt(uint32, uint32);
obj* l_Lean_Parser_Trie_empty(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6(obj*);
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(obj*, uint32);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg___boxed(obj*, obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_HasToString(obj*);
obj* l_Lean_Parser_Trie_insert___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Trie_HasEmptyc___closed__1;
obj* l_Lean_Parser_Trie_matchPrefix(obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_3__findAux___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1(obj*, obj*);
namespace lean {
obj* format_group_core(obj*);
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux(obj*);
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1(obj*);
obj* l_Lean_Parser_Trie_empty___closed__1;
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(obj*, uint32, obj*);
obj* l_RBNode_setBlack___rarg(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(obj*, uint32, obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l___private_init_lean_parser_trie_6__toStringAux___main___rarg(obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(obj*, uint32, obj*);
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(obj*, uint32, obj*);
obj* l___private_init_lean_parser_trie_6__toStringAux___main(obj*);
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_find___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7(obj*);
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_insert(obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj*, obj*, obj*, obj*);
obj* _init_l_Lean_Parser_Trie_empty___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Trie_empty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Trie_empty___closed__1;
return x_2;
}
}
obj* _init_l_Lean_Parser_Trie_HasEmptyc___closed__1() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Trie_empty(lean::box(0));
return x_1;
}
}
obj* l_Lean_Parser_Trie_HasEmptyc(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
return x_2;
}
}
obj* l_Lean_Parser_Trie_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Trie_empty___closed__1;
return x_2;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::string_utf8_get(x_1, x_3);
x_6 = lean::string_utf8_next(x_1, x_3);
x_7 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_6);
lean::dec(x_6);
x_8 = lean::box(0);
x_9 = lean::box_uint32(x_5);
x_10 = l_RBNode_singleton___rarg(x_9, x_7);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_2);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_1__insertEmptyAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_1__insertEmptyAux___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(obj* x_1, uint32 x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint32 x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::unbox_uint32(x_5);
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
lean::dec(x_4);
x_10 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_11 = x_10 < x_2;
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_6);
return x_12;
}
else
{
lean::dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::box_uint32(x_2);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
x_13 = lean::unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = lean::unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_17);
return x_1;
}
else
{
obj* x_18; 
x_18 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_12, x_2, x_3);
lean::cnstr_set(x_1, 3, x_18);
return x_1;
}
}
else
{
obj* x_19; 
x_19 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_9, x_2, x_3);
lean::cnstr_set(x_1, 0, x_19);
return x_1;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint32 x_24; uint8 x_25; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_1);
x_24 = lean::unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = lean::unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_21);
x_28 = lean::box_uint32(x_2);
x_29 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_29, 0, x_20);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_29, 2, x_3);
lean::cnstr_set(x_29, 3, x_23);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_23, x_2, x_3);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_21);
lean::cnstr_set(x_31, 2, x_22);
lean::cnstr_set(x_31, 3, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_20, x_2, x_3);
x_33 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_21);
lean::cnstr_set(x_33, 2, x_22);
lean::cnstr_set(x_33, 3, x_23);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_1);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint32 x_39; uint8 x_40; 
x_35 = lean::cnstr_get(x_1, 0);
x_36 = lean::cnstr_get(x_1, 1);
x_37 = lean::cnstr_get(x_1, 2);
x_38 = lean::cnstr_get(x_1, 3);
x_39 = lean::unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = lean::unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
obj* x_43; 
lean::dec(x_37);
lean::dec(x_36);
x_43 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
obj* x_45; 
x_45 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_38, x_2, x_3);
lean::cnstr_set(x_1, 3, x_45);
return x_1;
}
else
{
obj* x_46; 
x_46 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_38, x_2, x_3);
if (lean::obj_tag(x_46) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_35);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; 
x_48 = lean::cnstr_get(x_46, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_46);
if (x_49 == 0)
{
obj* x_50; obj* x_51; uint8 x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_46, 3);
lean::dec(x_50);
x_51 = lean::cnstr_get(x_46, 0);
lean::dec(x_51);
x_52 = 0;
lean::cnstr_set(x_46, 0, x_48);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
obj* x_54; obj* x_55; uint8 x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_46, 1);
x_55 = lean::cnstr_get(x_46, 2);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_46);
x_56 = 0;
x_57 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_57, 0, x_48);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_55);
lean::cnstr_set(x_57, 3, x_48);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean::cnstr_set(x_1, 3, x_57);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8 x_59; 
x_59 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_46);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_61 = lean::cnstr_get(x_46, 1);
x_62 = lean::cnstr_get(x_46, 2);
x_63 = lean::cnstr_get(x_46, 3);
lean::dec(x_63);
x_64 = lean::cnstr_get(x_46, 0);
lean::dec(x_64);
x_65 = !lean::is_exclusive(x_48);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; uint8 x_70; 
x_66 = lean::cnstr_get(x_48, 0);
x_67 = lean::cnstr_get(x_48, 1);
x_68 = lean::cnstr_get(x_48, 2);
x_69 = lean::cnstr_get(x_48, 3);
x_70 = 1;
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set(x_48, 2, x_37);
lean::cnstr_set(x_48, 1, x_36);
lean::cnstr_set(x_48, 0, x_35);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_70);
lean::cnstr_set(x_46, 3, x_69);
lean::cnstr_set(x_46, 2, x_68);
lean::cnstr_set(x_46, 1, x_67);
lean::cnstr_set(x_46, 0, x_66);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_70);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_48);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; uint8 x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_48, 0);
x_72 = lean::cnstr_get(x_48, 1);
x_73 = lean::cnstr_get(x_48, 2);
x_74 = lean::cnstr_get(x_48, 3);
lean::inc(x_74);
lean::inc(x_73);
lean::inc(x_72);
lean::inc(x_71);
lean::dec(x_48);
x_75 = 1;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_35);
lean::cnstr_set(x_76, 1, x_36);
lean::cnstr_set(x_76, 2, x_37);
lean::cnstr_set(x_76, 3, x_47);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_75);
lean::cnstr_set(x_46, 3, x_74);
lean::cnstr_set(x_46, 2, x_73);
lean::cnstr_set(x_46, 1, x_72);
lean::cnstr_set(x_46, 0, x_71);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_75);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_76);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; 
x_77 = lean::cnstr_get(x_46, 1);
x_78 = lean::cnstr_get(x_46, 2);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_48, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_48, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_48, 2);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_48, 3);
lean::inc(x_82);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 lean::cnstr_release(x_48, 2);
 lean::cnstr_release(x_48, 3);
 x_83 = x_48;
} else {
 lean::dec_ref(x_48);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_35);
lean::cnstr_set(x_85, 1, x_36);
lean::cnstr_set(x_85, 2, x_37);
lean::cnstr_set(x_85, 3, x_47);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_79);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_81);
lean::cnstr_set(x_86, 3, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_84);
lean::cnstr_set(x_1, 3, x_86);
lean::cnstr_set(x_1, 2, x_78);
lean::cnstr_set(x_1, 1, x_77);
lean::cnstr_set(x_1, 0, x_85);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_46);
if (x_87 == 0)
{
obj* x_88; obj* x_89; uint8 x_90; 
x_88 = lean::cnstr_get(x_46, 3);
lean::dec(x_88);
x_89 = lean::cnstr_get(x_46, 0);
lean::dec(x_89);
x_90 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_90);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_91; obj* x_92; uint8 x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_46, 1);
x_92 = lean::cnstr_get(x_46, 2);
lean::inc(x_92);
lean::inc(x_91);
lean::dec(x_46);
x_93 = 0;
x_94 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_94, 0, x_47);
lean::cnstr_set(x_94, 1, x_91);
lean::cnstr_set(x_94, 2, x_92);
lean::cnstr_set(x_94, 3, x_48);
lean::cnstr_set_scalar(x_94, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_94);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8 x_95; 
x_95 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8 x_96; 
x_96 = !lean::is_exclusive(x_46);
if (x_96 == 0)
{
obj* x_97; uint8 x_98; 
x_97 = lean::cnstr_get(x_46, 0);
lean::dec(x_97);
x_98 = !lean::is_exclusive(x_47);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; uint8 x_103; 
x_99 = lean::cnstr_get(x_47, 0);
x_100 = lean::cnstr_get(x_47, 1);
x_101 = lean::cnstr_get(x_47, 2);
x_102 = lean::cnstr_get(x_47, 3);
x_103 = 1;
lean::cnstr_set(x_47, 3, x_99);
lean::cnstr_set(x_47, 2, x_37);
lean::cnstr_set(x_47, 1, x_36);
lean::cnstr_set(x_47, 0, x_35);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_103);
lean::cnstr_set(x_46, 0, x_102);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_103);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_101);
lean::cnstr_set(x_1, 1, x_100);
lean::cnstr_set(x_1, 0, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_47, 0);
x_105 = lean::cnstr_get(x_47, 1);
x_106 = lean::cnstr_get(x_47, 2);
x_107 = lean::cnstr_get(x_47, 3);
lean::inc(x_107);
lean::inc(x_106);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_47);
x_108 = 1;
x_109 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_109, 0, x_35);
lean::cnstr_set(x_109, 1, x_36);
lean::cnstr_set(x_109, 2, x_37);
lean::cnstr_set(x_109, 3, x_104);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
lean::cnstr_set(x_46, 0, x_107);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_106);
lean::cnstr_set(x_1, 1, x_105);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; 
x_110 = lean::cnstr_get(x_46, 1);
x_111 = lean::cnstr_get(x_46, 2);
x_112 = lean::cnstr_get(x_46, 3);
lean::inc(x_112);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_46);
x_113 = lean::cnstr_get(x_47, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_47, 1);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_47, 2);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_47, 3);
lean::inc(x_116);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_117 = x_47;
} else {
 lean::dec_ref(x_47);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_35);
lean::cnstr_set(x_119, 1, x_36);
lean::cnstr_set(x_119, 2, x_37);
lean::cnstr_set(x_119, 3, x_113);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set(x_120, 1, x_110);
lean::cnstr_set(x_120, 2, x_111);
lean::cnstr_set(x_120, 3, x_112);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_120);
lean::cnstr_set(x_1, 2, x_115);
lean::cnstr_set(x_1, 1, x_114);
lean::cnstr_set(x_1, 0, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_46, 3);
lean::inc(x_121);
if (lean::obj_tag(x_121) == 0)
{
uint8 x_122; 
x_122 = !lean::is_exclusive(x_46);
if (x_122 == 0)
{
obj* x_123; obj* x_124; uint8 x_125; 
x_123 = lean::cnstr_get(x_46, 3);
lean::dec(x_123);
x_124 = lean::cnstr_get(x_46, 0);
lean::dec(x_124);
x_125 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_125);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_126; obj* x_127; uint8 x_128; obj* x_129; 
x_126 = lean::cnstr_get(x_46, 1);
x_127 = lean::cnstr_get(x_46, 2);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_46);
x_128 = 0;
x_129 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_129, 0, x_47);
lean::cnstr_set(x_129, 1, x_126);
lean::cnstr_set(x_129, 2, x_127);
lean::cnstr_set(x_129, 3, x_121);
lean::cnstr_set_scalar(x_129, sizeof(void*)*4, x_128);
lean::cnstr_set(x_1, 3, x_129);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8 x_130; 
x_130 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8 x_131; 
lean::free_heap_obj(x_1);
x_131 = !lean::is_exclusive(x_46);
if (x_131 == 0)
{
obj* x_132; obj* x_133; uint8 x_134; 
x_132 = lean::cnstr_get(x_46, 3);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_46, 0);
lean::dec(x_133);
x_134 = !lean::is_exclusive(x_121);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; uint8 x_139; 
x_135 = lean::cnstr_get(x_121, 0);
x_136 = lean::cnstr_get(x_121, 1);
x_137 = lean::cnstr_get(x_121, 2);
x_138 = lean::cnstr_get(x_121, 3);
lean::inc(x_47);
lean::cnstr_set(x_121, 3, x_47);
lean::cnstr_set(x_121, 2, x_37);
lean::cnstr_set(x_121, 1, x_36);
lean::cnstr_set(x_121, 0, x_35);
x_139 = !lean::is_exclusive(x_47);
if (x_139 == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_140 = lean::cnstr_get(x_47, 3);
lean::dec(x_140);
x_141 = lean::cnstr_get(x_47, 2);
lean::dec(x_141);
x_142 = lean::cnstr_get(x_47, 1);
lean::dec(x_142);
x_143 = lean::cnstr_get(x_47, 0);
lean::dec(x_143);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
lean::cnstr_set(x_47, 3, x_138);
lean::cnstr_set(x_47, 2, x_137);
lean::cnstr_set(x_47, 1, x_136);
lean::cnstr_set(x_47, 0, x_135);
lean::cnstr_set(x_46, 3, x_47);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
obj* x_144; 
lean::dec(x_47);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
x_144 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_144, 0, x_135);
lean::cnstr_set(x_144, 1, x_136);
lean::cnstr_set(x_144, 2, x_137);
lean::cnstr_set(x_144, 3, x_138);
lean::cnstr_set_scalar(x_144, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_144);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_121, 0);
x_146 = lean::cnstr_get(x_121, 1);
x_147 = lean::cnstr_get(x_121, 2);
x_148 = lean::cnstr_get(x_121, 3);
lean::inc(x_148);
lean::inc(x_147);
lean::inc(x_146);
lean::inc(x_145);
lean::dec(x_121);
lean::inc(x_47);
x_149 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_149, 0, x_35);
lean::cnstr_set(x_149, 1, x_36);
lean::cnstr_set(x_149, 2, x_37);
lean::cnstr_set(x_149, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_150 = x_47;
} else {
 lean::dec_ref(x_47);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_145);
lean::cnstr_set(x_151, 1, x_146);
lean::cnstr_set(x_151, 2, x_147);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_151);
lean::cnstr_set(x_46, 0, x_149);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_152 = lean::cnstr_get(x_46, 1);
x_153 = lean::cnstr_get(x_46, 2);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_46);
x_154 = lean::cnstr_get(x_121, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_121, 1);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_121, 2);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_121, 3);
lean::inc(x_157);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 lean::cnstr_release(x_121, 2);
 lean::cnstr_release(x_121, 3);
 x_158 = x_121;
} else {
 lean::dec_ref(x_121);
 x_158 = lean::box(0);
}
lean::inc(x_47);
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_35);
lean::cnstr_set(x_159, 1, x_36);
lean::cnstr_set(x_159, 2, x_37);
lean::cnstr_set(x_159, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_160 = x_47;
} else {
 lean::dec_ref(x_47);
 x_160 = lean::box(0);
}
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_154);
lean::cnstr_set(x_161, 1, x_155);
lean::cnstr_set(x_161, 2, x_156);
lean::cnstr_set(x_161, 3, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*4, x_95);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_152);
lean::cnstr_set(x_162, 2, x_153);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8 x_163; 
x_163 = !lean::is_exclusive(x_46);
if (x_163 == 0)
{
obj* x_164; obj* x_165; uint8 x_166; 
x_164 = lean::cnstr_get(x_46, 3);
lean::dec(x_164);
x_165 = lean::cnstr_get(x_46, 0);
lean::dec(x_165);
x_166 = !lean::is_exclusive(x_47);
if (x_166 == 0)
{
uint8 x_167; 
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_167);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; uint8 x_173; 
x_168 = lean::cnstr_get(x_47, 0);
x_169 = lean::cnstr_get(x_47, 1);
x_170 = lean::cnstr_get(x_47, 2);
x_171 = lean::cnstr_get(x_47, 3);
lean::inc(x_171);
lean::inc(x_170);
lean::inc(x_169);
lean::inc(x_168);
lean::dec(x_47);
x_172 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set(x_172, 1, x_169);
lean::cnstr_set(x_172, 2, x_170);
lean::cnstr_set(x_172, 3, x_171);
lean::cnstr_set_scalar(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean::cnstr_set(x_46, 0, x_172);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_173);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; 
x_174 = lean::cnstr_get(x_46, 1);
x_175 = lean::cnstr_get(x_46, 2);
lean::inc(x_175);
lean::inc(x_174);
lean::dec(x_46);
x_176 = lean::cnstr_get(x_47, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_47, 1);
lean::inc(x_177);
x_178 = lean::cnstr_get(x_47, 2);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_47, 3);
lean::inc(x_179);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_180 = x_47;
} else {
 lean::dec_ref(x_47);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_176);
lean::cnstr_set(x_181, 1, x_177);
lean::cnstr_set(x_181, 2, x_178);
lean::cnstr_set(x_181, 3, x_179);
lean::cnstr_set_scalar(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_183, 0, x_181);
lean::cnstr_set(x_183, 1, x_174);
lean::cnstr_set(x_183, 2, x_175);
lean::cnstr_set(x_183, 3, x_121);
lean::cnstr_set_scalar(x_183, sizeof(void*)*4, x_182);
lean::cnstr_set(x_1, 3, x_183);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
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
uint8 x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
obj* x_185; 
x_185 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_35, x_2, x_3);
lean::cnstr_set(x_1, 0, x_185);
return x_1;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_35, x_2, x_3);
if (lean::obj_tag(x_186) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_38);
lean::dec(x_37);
lean::dec(x_36);
return x_186;
}
else
{
obj* x_187; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; 
x_188 = lean::cnstr_get(x_186, 3);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
uint8 x_189; 
x_189 = !lean::is_exclusive(x_186);
if (x_189 == 0)
{
obj* x_190; obj* x_191; uint8 x_192; uint8 x_193; 
x_190 = lean::cnstr_get(x_186, 3);
lean::dec(x_190);
x_191 = lean::cnstr_get(x_186, 0);
lean::dec(x_191);
x_192 = 0;
lean::cnstr_set(x_186, 0, x_188);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
obj* x_194; obj* x_195; uint8 x_196; obj* x_197; uint8 x_198; 
x_194 = lean::cnstr_get(x_186, 1);
x_195 = lean::cnstr_get(x_186, 2);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_186);
x_196 = 0;
x_197 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_197, 0, x_188);
lean::cnstr_set(x_197, 1, x_194);
lean::cnstr_set(x_197, 2, x_195);
lean::cnstr_set(x_197, 3, x_188);
lean::cnstr_set_scalar(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean::cnstr_set(x_1, 0, x_197);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8 x_199; 
x_199 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8 x_200; 
x_200 = !lean::is_exclusive(x_186);
if (x_200 == 0)
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; 
x_201 = lean::cnstr_get(x_186, 1);
x_202 = lean::cnstr_get(x_186, 2);
x_203 = lean::cnstr_get(x_186, 3);
lean::dec(x_203);
x_204 = lean::cnstr_get(x_186, 0);
lean::dec(x_204);
x_205 = !lean::is_exclusive(x_188);
if (x_205 == 0)
{
obj* x_206; obj* x_207; obj* x_208; obj* x_209; uint8 x_210; 
x_206 = lean::cnstr_get(x_188, 0);
x_207 = lean::cnstr_get(x_188, 1);
x_208 = lean::cnstr_get(x_188, 2);
x_209 = lean::cnstr_get(x_188, 3);
x_210 = 1;
lean::cnstr_set(x_188, 3, x_206);
lean::cnstr_set(x_188, 2, x_202);
lean::cnstr_set(x_188, 1, x_201);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set_scalar(x_188, sizeof(void*)*4, x_210);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_209);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_210);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_208);
lean::cnstr_set(x_1, 1, x_207);
lean::cnstr_set(x_1, 0, x_188);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; uint8 x_215; obj* x_216; 
x_211 = lean::cnstr_get(x_188, 0);
x_212 = lean::cnstr_get(x_188, 1);
x_213 = lean::cnstr_get(x_188, 2);
x_214 = lean::cnstr_get(x_188, 3);
lean::inc(x_214);
lean::inc(x_213);
lean::inc(x_212);
lean::inc(x_211);
lean::dec(x_188);
x_215 = 1;
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_187);
lean::cnstr_set(x_216, 1, x_201);
lean::cnstr_set(x_216, 2, x_202);
lean::cnstr_set(x_216, 3, x_211);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_215);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_214);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_215);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_213);
lean::cnstr_set(x_1, 1, x_212);
lean::cnstr_set(x_1, 0, x_216);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; uint8 x_224; obj* x_225; obj* x_226; 
x_217 = lean::cnstr_get(x_186, 1);
x_218 = lean::cnstr_get(x_186, 2);
lean::inc(x_218);
lean::inc(x_217);
lean::dec(x_186);
x_219 = lean::cnstr_get(x_188, 0);
lean::inc(x_219);
x_220 = lean::cnstr_get(x_188, 1);
lean::inc(x_220);
x_221 = lean::cnstr_get(x_188, 2);
lean::inc(x_221);
x_222 = lean::cnstr_get(x_188, 3);
lean::inc(x_222);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 lean::cnstr_release(x_188, 2);
 lean::cnstr_release(x_188, 3);
 x_223 = x_188;
} else {
 lean::dec_ref(x_188);
 x_223 = lean::box(0);
}
x_224 = 1;
if (lean::is_scalar(x_223)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_223;
}
lean::cnstr_set(x_225, 0, x_187);
lean::cnstr_set(x_225, 1, x_217);
lean::cnstr_set(x_225, 2, x_218);
lean::cnstr_set(x_225, 3, x_219);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_224);
x_226 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set(x_226, 1, x_36);
lean::cnstr_set(x_226, 2, x_37);
lean::cnstr_set(x_226, 3, x_38);
lean::cnstr_set_scalar(x_226, sizeof(void*)*4, x_224);
lean::cnstr_set(x_1, 3, x_226);
lean::cnstr_set(x_1, 2, x_221);
lean::cnstr_set(x_1, 1, x_220);
lean::cnstr_set(x_1, 0, x_225);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8 x_227; 
x_227 = !lean::is_exclusive(x_186);
if (x_227 == 0)
{
obj* x_228; obj* x_229; uint8 x_230; 
x_228 = lean::cnstr_get(x_186, 3);
lean::dec(x_228);
x_229 = lean::cnstr_get(x_186, 0);
lean::dec(x_229);
x_230 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_230);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_231; obj* x_232; uint8 x_233; obj* x_234; 
x_231 = lean::cnstr_get(x_186, 1);
x_232 = lean::cnstr_get(x_186, 2);
lean::inc(x_232);
lean::inc(x_231);
lean::dec(x_186);
x_233 = 0;
x_234 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_234, 0, x_187);
lean::cnstr_set(x_234, 1, x_231);
lean::cnstr_set(x_234, 2, x_232);
lean::cnstr_set(x_234, 3, x_188);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 0, x_234);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8 x_235; 
x_235 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8 x_236; 
x_236 = !lean::is_exclusive(x_186);
if (x_236 == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; uint8 x_241; 
x_237 = lean::cnstr_get(x_186, 1);
x_238 = lean::cnstr_get(x_186, 2);
x_239 = lean::cnstr_get(x_186, 3);
x_240 = lean::cnstr_get(x_186, 0);
lean::dec(x_240);
x_241 = !lean::is_exclusive(x_187);
if (x_241 == 0)
{
uint8 x_242; 
x_242 = 1;
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_242);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_242);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; 
x_243 = lean::cnstr_get(x_187, 0);
x_244 = lean::cnstr_get(x_187, 1);
x_245 = lean::cnstr_get(x_187, 2);
x_246 = lean::cnstr_get(x_187, 3);
lean::inc(x_246);
lean::inc(x_245);
lean::inc(x_244);
lean::inc(x_243);
lean::dec(x_187);
x_247 = 1;
x_248 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_248, 0, x_243);
lean::cnstr_set(x_248, 1, x_244);
lean::cnstr_set(x_248, 2, x_245);
lean::cnstr_set(x_248, 3, x_246);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; uint8 x_257; obj* x_258; obj* x_259; 
x_249 = lean::cnstr_get(x_186, 1);
x_250 = lean::cnstr_get(x_186, 2);
x_251 = lean::cnstr_get(x_186, 3);
lean::inc(x_251);
lean::inc(x_250);
lean::inc(x_249);
lean::dec(x_186);
x_252 = lean::cnstr_get(x_187, 0);
lean::inc(x_252);
x_253 = lean::cnstr_get(x_187, 1);
lean::inc(x_253);
x_254 = lean::cnstr_get(x_187, 2);
lean::inc(x_254);
x_255 = lean::cnstr_get(x_187, 3);
lean::inc(x_255);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_256 = x_187;
} else {
 lean::dec_ref(x_187);
 x_256 = lean::box(0);
}
x_257 = 1;
if (lean::is_scalar(x_256)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_256;
}
lean::cnstr_set(x_258, 0, x_252);
lean::cnstr_set(x_258, 1, x_253);
lean::cnstr_set(x_258, 2, x_254);
lean::cnstr_set(x_258, 3, x_255);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
x_259 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_259, 0, x_251);
lean::cnstr_set(x_259, 1, x_36);
lean::cnstr_set(x_259, 2, x_37);
lean::cnstr_set(x_259, 3, x_38);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 3, x_259);
lean::cnstr_set(x_1, 2, x_250);
lean::cnstr_set(x_1, 1, x_249);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_186, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
uint8 x_261; 
x_261 = !lean::is_exclusive(x_186);
if (x_261 == 0)
{
obj* x_262; obj* x_263; uint8 x_264; 
x_262 = lean::cnstr_get(x_186, 3);
lean::dec(x_262);
x_263 = lean::cnstr_get(x_186, 0);
lean::dec(x_263);
x_264 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_264);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_265; obj* x_266; uint8 x_267; obj* x_268; 
x_265 = lean::cnstr_get(x_186, 1);
x_266 = lean::cnstr_get(x_186, 2);
lean::inc(x_266);
lean::inc(x_265);
lean::dec(x_186);
x_267 = 0;
x_268 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_268, 0, x_187);
lean::cnstr_set(x_268, 1, x_265);
lean::cnstr_set(x_268, 2, x_266);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
lean::cnstr_set(x_1, 0, x_268);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8 x_269; 
x_269 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8 x_270; 
lean::free_heap_obj(x_1);
x_270 = !lean::is_exclusive(x_186);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; uint8 x_275; 
x_271 = lean::cnstr_get(x_186, 1);
x_272 = lean::cnstr_get(x_186, 2);
x_273 = lean::cnstr_get(x_186, 3);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_186, 0);
lean::dec(x_274);
x_275 = !lean::is_exclusive(x_260);
if (x_275 == 0)
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; uint8 x_280; 
x_276 = lean::cnstr_get(x_260, 0);
x_277 = lean::cnstr_get(x_260, 1);
x_278 = lean::cnstr_get(x_260, 2);
x_279 = lean::cnstr_get(x_260, 3);
lean::inc(x_187);
lean::cnstr_set(x_260, 3, x_276);
lean::cnstr_set(x_260, 2, x_272);
lean::cnstr_set(x_260, 1, x_271);
lean::cnstr_set(x_260, 0, x_187);
x_280 = !lean::is_exclusive(x_187);
if (x_280 == 0)
{
obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_281 = lean::cnstr_get(x_187, 3);
lean::dec(x_281);
x_282 = lean::cnstr_get(x_187, 2);
lean::dec(x_282);
x_283 = lean::cnstr_get(x_187, 1);
lean::dec(x_283);
x_284 = lean::cnstr_get(x_187, 0);
lean::dec(x_284);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
lean::cnstr_set(x_187, 3, x_38);
lean::cnstr_set(x_187, 2, x_37);
lean::cnstr_set(x_187, 1, x_36);
lean::cnstr_set(x_187, 0, x_279);
lean::cnstr_set(x_186, 3, x_187);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
obj* x_285; 
lean::dec(x_187);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
x_285 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_285, 0, x_279);
lean::cnstr_set(x_285, 1, x_36);
lean::cnstr_set(x_285, 2, x_37);
lean::cnstr_set(x_285, 3, x_38);
lean::cnstr_set_scalar(x_285, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_285);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
x_286 = lean::cnstr_get(x_260, 0);
x_287 = lean::cnstr_get(x_260, 1);
x_288 = lean::cnstr_get(x_260, 2);
x_289 = lean::cnstr_get(x_260, 3);
lean::inc(x_289);
lean::inc(x_288);
lean::inc(x_287);
lean::inc(x_286);
lean::dec(x_260);
lean::inc(x_187);
x_290 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_290, 0, x_187);
lean::cnstr_set(x_290, 1, x_271);
lean::cnstr_set(x_290, 2, x_272);
lean::cnstr_set(x_290, 3, x_286);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_291 = x_187;
} else {
 lean::dec_ref(x_187);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_289);
lean::cnstr_set(x_292, 1, x_36);
lean::cnstr_set(x_292, 2, x_37);
lean::cnstr_set(x_292, 3, x_38);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_292);
lean::cnstr_set(x_186, 2, x_288);
lean::cnstr_set(x_186, 1, x_287);
lean::cnstr_set(x_186, 0, x_290);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_293 = lean::cnstr_get(x_186, 1);
x_294 = lean::cnstr_get(x_186, 2);
lean::inc(x_294);
lean::inc(x_293);
lean::dec(x_186);
x_295 = lean::cnstr_get(x_260, 0);
lean::inc(x_295);
x_296 = lean::cnstr_get(x_260, 1);
lean::inc(x_296);
x_297 = lean::cnstr_get(x_260, 2);
lean::inc(x_297);
x_298 = lean::cnstr_get(x_260, 3);
lean::inc(x_298);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 lean::cnstr_release(x_260, 2);
 lean::cnstr_release(x_260, 3);
 x_299 = x_260;
} else {
 lean::dec_ref(x_260);
 x_299 = lean::box(0);
}
lean::inc(x_187);
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_187);
lean::cnstr_set(x_300, 1, x_293);
lean::cnstr_set(x_300, 2, x_294);
lean::cnstr_set(x_300, 3, x_295);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_301 = x_187;
} else {
 lean::dec_ref(x_187);
 x_301 = lean::box(0);
}
lean::cnstr_set_scalar(x_300, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_301)) {
 x_302 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_302 = x_301;
}
lean::cnstr_set(x_302, 0, x_298);
lean::cnstr_set(x_302, 1, x_36);
lean::cnstr_set(x_302, 2, x_37);
lean::cnstr_set(x_302, 3, x_38);
lean::cnstr_set_scalar(x_302, sizeof(void*)*4, x_235);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_296);
lean::cnstr_set(x_303, 2, x_297);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8 x_304; 
x_304 = !lean::is_exclusive(x_186);
if (x_304 == 0)
{
obj* x_305; obj* x_306; uint8 x_307; 
x_305 = lean::cnstr_get(x_186, 3);
lean::dec(x_305);
x_306 = lean::cnstr_get(x_186, 0);
lean::dec(x_306);
x_307 = !lean::is_exclusive(x_187);
if (x_307 == 0)
{
uint8 x_308; 
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_308);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; uint8 x_314; 
x_309 = lean::cnstr_get(x_187, 0);
x_310 = lean::cnstr_get(x_187, 1);
x_311 = lean::cnstr_get(x_187, 2);
x_312 = lean::cnstr_get(x_187, 3);
lean::inc(x_312);
lean::inc(x_311);
lean::inc(x_310);
lean::inc(x_309);
lean::dec(x_187);
x_313 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_313, 0, x_309);
lean::cnstr_set(x_313, 1, x_310);
lean::cnstr_set(x_313, 2, x_311);
lean::cnstr_set(x_313, 3, x_312);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean::cnstr_set(x_186, 0, x_313);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_314);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; uint8 x_323; obj* x_324; 
x_315 = lean::cnstr_get(x_186, 1);
x_316 = lean::cnstr_get(x_186, 2);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_186);
x_317 = lean::cnstr_get(x_187, 0);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_187, 1);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_187, 2);
lean::inc(x_319);
x_320 = lean::cnstr_get(x_187, 3);
lean::inc(x_320);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_321 = x_187;
} else {
 lean::dec_ref(x_187);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_317);
lean::cnstr_set(x_322, 1, x_318);
lean::cnstr_set(x_322, 2, x_319);
lean::cnstr_set(x_322, 3, x_320);
lean::cnstr_set_scalar(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_322);
lean::cnstr_set(x_324, 1, x_315);
lean::cnstr_set(x_324, 2, x_316);
lean::cnstr_set(x_324, 3, x_260);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_323);
lean::cnstr_set(x_1, 0, x_324);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
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
obj* x_325; obj* x_326; obj* x_327; obj* x_328; uint32 x_329; uint8 x_330; 
x_325 = lean::cnstr_get(x_1, 0);
x_326 = lean::cnstr_get(x_1, 1);
x_327 = lean::cnstr_get(x_1, 2);
x_328 = lean::cnstr_get(x_1, 3);
lean::inc(x_328);
lean::inc(x_327);
lean::inc(x_326);
lean::inc(x_325);
lean::dec(x_1);
x_329 = lean::unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32 x_331; uint8 x_332; 
x_331 = lean::unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
obj* x_333; obj* x_334; 
lean::dec(x_327);
lean::dec(x_326);
x_333 = lean::box_uint32(x_2);
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_325);
lean::cnstr_set(x_334, 1, x_333);
lean::cnstr_set(x_334, 2, x_3);
lean::cnstr_set(x_334, 3, x_328);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8 x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
obj* x_336; obj* x_337; 
x_336 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_328, x_2, x_3);
x_337 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_337, 0, x_325);
lean::cnstr_set(x_337, 1, x_326);
lean::cnstr_set(x_337, 2, x_327);
lean::cnstr_set(x_337, 3, x_336);
lean::cnstr_set_scalar(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
obj* x_338; 
x_338 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_328, x_2, x_3);
if (lean::obj_tag(x_338) == 0)
{
lean::dec(x_327);
lean::dec(x_326);
lean::dec(x_325);
return x_338;
}
else
{
obj* x_339; 
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
if (lean::obj_tag(x_339) == 0)
{
obj* x_340; 
x_340 = lean::cnstr_get(x_338, 3);
lean::inc(x_340);
if (lean::obj_tag(x_340) == 0)
{
obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; uint8 x_346; obj* x_347; 
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_338, 2);
lean::inc(x_342);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_343 = x_338;
} else {
 lean::dec_ref(x_338);
 x_343 = lean::box(0);
}
x_344 = 0;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_340);
lean::cnstr_set(x_345, 1, x_341);
lean::cnstr_set(x_345, 2, x_342);
lean::cnstr_set(x_345, 3, x_340);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_325);
lean::cnstr_set(x_347, 1, x_326);
lean::cnstr_set(x_347, 2, x_327);
lean::cnstr_set(x_347, 3, x_345);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8 x_348; 
x_348 = lean::cnstr_get_scalar<uint8>(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; uint8 x_357; obj* x_358; obj* x_359; obj* x_360; 
x_349 = lean::cnstr_get(x_338, 1);
lean::inc(x_349);
x_350 = lean::cnstr_get(x_338, 2);
lean::inc(x_350);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_351 = x_338;
} else {
 lean::dec_ref(x_338);
 x_351 = lean::box(0);
}
x_352 = lean::cnstr_get(x_340, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_340, 1);
lean::inc(x_353);
x_354 = lean::cnstr_get(x_340, 2);
lean::inc(x_354);
x_355 = lean::cnstr_get(x_340, 3);
lean::inc(x_355);
if (lean::is_exclusive(x_340)) {
 lean::cnstr_release(x_340, 0);
 lean::cnstr_release(x_340, 1);
 lean::cnstr_release(x_340, 2);
 lean::cnstr_release(x_340, 3);
 x_356 = x_340;
} else {
 lean::dec_ref(x_340);
 x_356 = lean::box(0);
}
x_357 = 1;
if (lean::is_scalar(x_356)) {
 x_358 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_358 = x_356;
}
lean::cnstr_set(x_358, 0, x_325);
lean::cnstr_set(x_358, 1, x_326);
lean::cnstr_set(x_358, 2, x_327);
lean::cnstr_set(x_358, 3, x_339);
lean::cnstr_set_scalar(x_358, sizeof(void*)*4, x_357);
if (lean::is_scalar(x_351)) {
 x_359 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_359 = x_351;
}
lean::cnstr_set(x_359, 0, x_352);
lean::cnstr_set(x_359, 1, x_353);
lean::cnstr_set(x_359, 2, x_354);
lean::cnstr_set(x_359, 3, x_355);
lean::cnstr_set_scalar(x_359, sizeof(void*)*4, x_357);
x_360 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_360, 0, x_358);
lean::cnstr_set(x_360, 1, x_349);
lean::cnstr_set(x_360, 2, x_350);
lean::cnstr_set(x_360, 3, x_359);
lean::cnstr_set_scalar(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; 
x_361 = lean::cnstr_get(x_338, 1);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_338, 2);
lean::inc(x_362);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_363 = x_338;
} else {
 lean::dec_ref(x_338);
 x_363 = lean::box(0);
}
x_364 = 0;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_339);
lean::cnstr_set(x_365, 1, x_361);
lean::cnstr_set(x_365, 2, x_362);
lean::cnstr_set(x_365, 3, x_340);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
x_366 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_366, 0, x_325);
lean::cnstr_set(x_366, 1, x_326);
lean::cnstr_set(x_366, 2, x_327);
lean::cnstr_set(x_366, 3, x_365);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8 x_367; 
x_367 = lean::cnstr_get_scalar<uint8>(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; uint8 x_377; obj* x_378; obj* x_379; obj* x_380; 
x_368 = lean::cnstr_get(x_338, 1);
lean::inc(x_368);
x_369 = lean::cnstr_get(x_338, 2);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_338, 3);
lean::inc(x_370);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_371 = x_338;
} else {
 lean::dec_ref(x_338);
 x_371 = lean::box(0);
}
x_372 = lean::cnstr_get(x_339, 0);
lean::inc(x_372);
x_373 = lean::cnstr_get(x_339, 1);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_339, 2);
lean::inc(x_374);
x_375 = lean::cnstr_get(x_339, 3);
lean::inc(x_375);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_376 = x_339;
} else {
 lean::dec_ref(x_339);
 x_376 = lean::box(0);
}
x_377 = 1;
if (lean::is_scalar(x_376)) {
 x_378 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_378 = x_376;
}
lean::cnstr_set(x_378, 0, x_325);
lean::cnstr_set(x_378, 1, x_326);
lean::cnstr_set(x_378, 2, x_327);
lean::cnstr_set(x_378, 3, x_372);
lean::cnstr_set_scalar(x_378, sizeof(void*)*4, x_377);
if (lean::is_scalar(x_371)) {
 x_379 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_379 = x_371;
}
lean::cnstr_set(x_379, 0, x_375);
lean::cnstr_set(x_379, 1, x_368);
lean::cnstr_set(x_379, 2, x_369);
lean::cnstr_set(x_379, 3, x_370);
lean::cnstr_set_scalar(x_379, sizeof(void*)*4, x_377);
x_380 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_380, 0, x_378);
lean::cnstr_set(x_380, 1, x_373);
lean::cnstr_set(x_380, 2, x_374);
lean::cnstr_set(x_380, 3, x_379);
lean::cnstr_set_scalar(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
obj* x_381; 
x_381 = lean::cnstr_get(x_338, 3);
lean::inc(x_381);
if (lean::obj_tag(x_381) == 0)
{
obj* x_382; obj* x_383; obj* x_384; uint8 x_385; obj* x_386; obj* x_387; 
x_382 = lean::cnstr_get(x_338, 1);
lean::inc(x_382);
x_383 = lean::cnstr_get(x_338, 2);
lean::inc(x_383);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_384 = x_338;
} else {
 lean::dec_ref(x_338);
 x_384 = lean::box(0);
}
x_385 = 0;
if (lean::is_scalar(x_384)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_384;
}
lean::cnstr_set(x_386, 0, x_339);
lean::cnstr_set(x_386, 1, x_382);
lean::cnstr_set(x_386, 2, x_383);
lean::cnstr_set(x_386, 3, x_381);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_385);
x_387 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_387, 0, x_325);
lean::cnstr_set(x_387, 1, x_326);
lean::cnstr_set(x_387, 2, x_327);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8 x_388; 
x_388 = lean::cnstr_get_scalar<uint8>(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; 
x_389 = lean::cnstr_get(x_338, 1);
lean::inc(x_389);
x_390 = lean::cnstr_get(x_338, 2);
lean::inc(x_390);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_391 = x_338;
} else {
 lean::dec_ref(x_338);
 x_391 = lean::box(0);
}
x_392 = lean::cnstr_get(x_381, 0);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_381, 1);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_381, 2);
lean::inc(x_394);
x_395 = lean::cnstr_get(x_381, 3);
lean::inc(x_395);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 lean::cnstr_release(x_381, 1);
 lean::cnstr_release(x_381, 2);
 lean::cnstr_release(x_381, 3);
 x_396 = x_381;
} else {
 lean::dec_ref(x_381);
 x_396 = lean::box(0);
}
lean::inc(x_339);
if (lean::is_scalar(x_396)) {
 x_397 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_397 = x_396;
}
lean::cnstr_set(x_397, 0, x_325);
lean::cnstr_set(x_397, 1, x_326);
lean::cnstr_set(x_397, 2, x_327);
lean::cnstr_set(x_397, 3, x_339);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_398 = x_339;
} else {
 lean::dec_ref(x_339);
 x_398 = lean::box(0);
}
lean::cnstr_set_scalar(x_397, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_392);
lean::cnstr_set(x_399, 1, x_393);
lean::cnstr_set(x_399, 2, x_394);
lean::cnstr_set(x_399, 3, x_395);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_391)) {
 x_400 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_400 = x_391;
}
lean::cnstr_set(x_400, 0, x_397);
lean::cnstr_set(x_400, 1, x_389);
lean::cnstr_set(x_400, 2, x_390);
lean::cnstr_set(x_400, 3, x_399);
lean::cnstr_set_scalar(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; uint8 x_410; obj* x_411; obj* x_412; 
x_401 = lean::cnstr_get(x_338, 1);
lean::inc(x_401);
x_402 = lean::cnstr_get(x_338, 2);
lean::inc(x_402);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_403 = x_338;
} else {
 lean::dec_ref(x_338);
 x_403 = lean::box(0);
}
x_404 = lean::cnstr_get(x_339, 0);
lean::inc(x_404);
x_405 = lean::cnstr_get(x_339, 1);
lean::inc(x_405);
x_406 = lean::cnstr_get(x_339, 2);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_339, 3);
lean::inc(x_407);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_408 = x_339;
} else {
 lean::dec_ref(x_339);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_404);
lean::cnstr_set(x_409, 1, x_405);
lean::cnstr_set(x_409, 2, x_406);
lean::cnstr_set(x_409, 3, x_407);
lean::cnstr_set_scalar(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean::is_scalar(x_403)) {
 x_411 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_411 = x_403;
}
lean::cnstr_set(x_411, 0, x_409);
lean::cnstr_set(x_411, 1, x_401);
lean::cnstr_set(x_411, 2, x_402);
lean::cnstr_set(x_411, 3, x_381);
lean::cnstr_set_scalar(x_411, sizeof(void*)*4, x_410);
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_325);
lean::cnstr_set(x_412, 1, x_326);
lean::cnstr_set(x_412, 2, x_327);
lean::cnstr_set(x_412, 3, x_411);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_388);
return x_412;
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
uint8 x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
obj* x_414; obj* x_415; 
x_414 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_325, x_2, x_3);
x_415 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_415, 0, x_414);
lean::cnstr_set(x_415, 1, x_326);
lean::cnstr_set(x_415, 2, x_327);
lean::cnstr_set(x_415, 3, x_328);
lean::cnstr_set_scalar(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
obj* x_416; 
x_416 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_325, x_2, x_3);
if (lean::obj_tag(x_416) == 0)
{
lean::dec(x_328);
lean::dec(x_327);
lean::dec(x_326);
return x_416;
}
else
{
obj* x_417; 
x_417 = lean::cnstr_get(x_416, 0);
lean::inc(x_417);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; 
x_418 = lean::cnstr_get(x_416, 3);
lean::inc(x_418);
if (lean::obj_tag(x_418) == 0)
{
obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; uint8 x_424; obj* x_425; 
x_419 = lean::cnstr_get(x_416, 1);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_416, 2);
lean::inc(x_420);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_421 = x_416;
} else {
 lean::dec_ref(x_416);
 x_421 = lean::box(0);
}
x_422 = 0;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_418);
lean::cnstr_set(x_423, 1, x_419);
lean::cnstr_set(x_423, 2, x_420);
lean::cnstr_set(x_423, 3, x_418);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_326);
lean::cnstr_set(x_425, 2, x_327);
lean::cnstr_set(x_425, 3, x_328);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8 x_426; 
x_426 = lean::cnstr_get_scalar<uint8>(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; uint8 x_435; obj* x_436; obj* x_437; obj* x_438; 
x_427 = lean::cnstr_get(x_416, 1);
lean::inc(x_427);
x_428 = lean::cnstr_get(x_416, 2);
lean::inc(x_428);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_429 = x_416;
} else {
 lean::dec_ref(x_416);
 x_429 = lean::box(0);
}
x_430 = lean::cnstr_get(x_418, 0);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_418, 1);
lean::inc(x_431);
x_432 = lean::cnstr_get(x_418, 2);
lean::inc(x_432);
x_433 = lean::cnstr_get(x_418, 3);
lean::inc(x_433);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 lean::cnstr_release(x_418, 2);
 lean::cnstr_release(x_418, 3);
 x_434 = x_418;
} else {
 lean::dec_ref(x_418);
 x_434 = lean::box(0);
}
x_435 = 1;
if (lean::is_scalar(x_434)) {
 x_436 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_436 = x_434;
}
lean::cnstr_set(x_436, 0, x_417);
lean::cnstr_set(x_436, 1, x_427);
lean::cnstr_set(x_436, 2, x_428);
lean::cnstr_set(x_436, 3, x_430);
lean::cnstr_set_scalar(x_436, sizeof(void*)*4, x_435);
if (lean::is_scalar(x_429)) {
 x_437 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_437 = x_429;
}
lean::cnstr_set(x_437, 0, x_433);
lean::cnstr_set(x_437, 1, x_326);
lean::cnstr_set(x_437, 2, x_327);
lean::cnstr_set(x_437, 3, x_328);
lean::cnstr_set_scalar(x_437, sizeof(void*)*4, x_435);
x_438 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_438, 0, x_436);
lean::cnstr_set(x_438, 1, x_431);
lean::cnstr_set(x_438, 2, x_432);
lean::cnstr_set(x_438, 3, x_437);
lean::cnstr_set_scalar(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; 
x_439 = lean::cnstr_get(x_416, 1);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_416, 2);
lean::inc(x_440);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_441 = x_416;
} else {
 lean::dec_ref(x_416);
 x_441 = lean::box(0);
}
x_442 = 0;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_417);
lean::cnstr_set(x_443, 1, x_439);
lean::cnstr_set(x_443, 2, x_440);
lean::cnstr_set(x_443, 3, x_418);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
x_444 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_444, 0, x_443);
lean::cnstr_set(x_444, 1, x_326);
lean::cnstr_set(x_444, 2, x_327);
lean::cnstr_set(x_444, 3, x_328);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8 x_445; 
x_445 = lean::cnstr_get_scalar<uint8>(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; 
x_446 = lean::cnstr_get(x_416, 1);
lean::inc(x_446);
x_447 = lean::cnstr_get(x_416, 2);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_416, 3);
lean::inc(x_448);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_449 = x_416;
} else {
 lean::dec_ref(x_416);
 x_449 = lean::box(0);
}
x_450 = lean::cnstr_get(x_417, 0);
lean::inc(x_450);
x_451 = lean::cnstr_get(x_417, 1);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_417, 2);
lean::inc(x_452);
x_453 = lean::cnstr_get(x_417, 3);
lean::inc(x_453);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_454 = x_417;
} else {
 lean::dec_ref(x_417);
 x_454 = lean::box(0);
}
x_455 = 1;
if (lean::is_scalar(x_454)) {
 x_456 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_456 = x_454;
}
lean::cnstr_set(x_456, 0, x_450);
lean::cnstr_set(x_456, 1, x_451);
lean::cnstr_set(x_456, 2, x_452);
lean::cnstr_set(x_456, 3, x_453);
lean::cnstr_set_scalar(x_456, sizeof(void*)*4, x_455);
if (lean::is_scalar(x_449)) {
 x_457 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_457 = x_449;
}
lean::cnstr_set(x_457, 0, x_448);
lean::cnstr_set(x_457, 1, x_326);
lean::cnstr_set(x_457, 2, x_327);
lean::cnstr_set(x_457, 3, x_328);
lean::cnstr_set_scalar(x_457, sizeof(void*)*4, x_455);
x_458 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_458, 0, x_456);
lean::cnstr_set(x_458, 1, x_446);
lean::cnstr_set(x_458, 2, x_447);
lean::cnstr_set(x_458, 3, x_457);
lean::cnstr_set_scalar(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
obj* x_459; 
x_459 = lean::cnstr_get(x_416, 3);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_460; obj* x_461; obj* x_462; uint8 x_463; obj* x_464; obj* x_465; 
x_460 = lean::cnstr_get(x_416, 1);
lean::inc(x_460);
x_461 = lean::cnstr_get(x_416, 2);
lean::inc(x_461);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_462 = x_416;
} else {
 lean::dec_ref(x_416);
 x_462 = lean::box(0);
}
x_463 = 0;
if (lean::is_scalar(x_462)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_462;
}
lean::cnstr_set(x_464, 0, x_417);
lean::cnstr_set(x_464, 1, x_460);
lean::cnstr_set(x_464, 2, x_461);
lean::cnstr_set(x_464, 3, x_459);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_463);
x_465 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_326);
lean::cnstr_set(x_465, 2, x_327);
lean::cnstr_set(x_465, 3, x_328);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8 x_466; 
x_466 = lean::cnstr_get_scalar<uint8>(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; 
x_467 = lean::cnstr_get(x_416, 1);
lean::inc(x_467);
x_468 = lean::cnstr_get(x_416, 2);
lean::inc(x_468);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_469 = x_416;
} else {
 lean::dec_ref(x_416);
 x_469 = lean::box(0);
}
x_470 = lean::cnstr_get(x_459, 0);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_459, 1);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_459, 2);
lean::inc(x_472);
x_473 = lean::cnstr_get(x_459, 3);
lean::inc(x_473);
if (lean::is_exclusive(x_459)) {
 lean::cnstr_release(x_459, 0);
 lean::cnstr_release(x_459, 1);
 lean::cnstr_release(x_459, 2);
 lean::cnstr_release(x_459, 3);
 x_474 = x_459;
} else {
 lean::dec_ref(x_459);
 x_474 = lean::box(0);
}
lean::inc(x_417);
if (lean::is_scalar(x_474)) {
 x_475 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_475 = x_474;
}
lean::cnstr_set(x_475, 0, x_417);
lean::cnstr_set(x_475, 1, x_467);
lean::cnstr_set(x_475, 2, x_468);
lean::cnstr_set(x_475, 3, x_470);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_476 = x_417;
} else {
 lean::dec_ref(x_417);
 x_476 = lean::box(0);
}
lean::cnstr_set_scalar(x_475, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_476)) {
 x_477 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_477 = x_476;
}
lean::cnstr_set(x_477, 0, x_473);
lean::cnstr_set(x_477, 1, x_326);
lean::cnstr_set(x_477, 2, x_327);
lean::cnstr_set(x_477, 3, x_328);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_469)) {
 x_478 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_478 = x_469;
}
lean::cnstr_set(x_478, 0, x_475);
lean::cnstr_set(x_478, 1, x_471);
lean::cnstr_set(x_478, 2, x_472);
lean::cnstr_set(x_478, 3, x_477);
lean::cnstr_set_scalar(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; uint8 x_488; obj* x_489; obj* x_490; 
x_479 = lean::cnstr_get(x_416, 1);
lean::inc(x_479);
x_480 = lean::cnstr_get(x_416, 2);
lean::inc(x_480);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_481 = x_416;
} else {
 lean::dec_ref(x_416);
 x_481 = lean::box(0);
}
x_482 = lean::cnstr_get(x_417, 0);
lean::inc(x_482);
x_483 = lean::cnstr_get(x_417, 1);
lean::inc(x_483);
x_484 = lean::cnstr_get(x_417, 2);
lean::inc(x_484);
x_485 = lean::cnstr_get(x_417, 3);
lean::inc(x_485);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_486 = x_417;
} else {
 lean::dec_ref(x_417);
 x_486 = lean::box(0);
}
if (lean::is_scalar(x_486)) {
 x_487 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_487 = x_486;
}
lean::cnstr_set(x_487, 0, x_482);
lean::cnstr_set(x_487, 1, x_483);
lean::cnstr_set(x_487, 2, x_484);
lean::cnstr_set(x_487, 3, x_485);
lean::cnstr_set_scalar(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean::is_scalar(x_481)) {
 x_489 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_489 = x_481;
}
lean::cnstr_set(x_489, 0, x_487);
lean::cnstr_set(x_489, 1, x_479);
lean::cnstr_set(x_489, 2, x_480);
lean::cnstr_set(x_489, 3, x_459);
lean::cnstr_set_scalar(x_489, sizeof(void*)*4, x_488);
x_490 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_490, 0, x_489);
lean::cnstr_set(x_490, 1, x_326);
lean::cnstr_set(x_490, 2, x_327);
lean::cnstr_set(x_490, 3, x_328);
lean::cnstr_set_scalar(x_490, sizeof(void*)*4, x_466);
return x_490;
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
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::box_uint32(x_2);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
x_13 = lean::unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = lean::unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_17);
return x_1;
}
else
{
obj* x_18; 
x_18 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_12, x_2, x_3);
lean::cnstr_set(x_1, 3, x_18);
return x_1;
}
}
else
{
obj* x_19; 
x_19 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_9, x_2, x_3);
lean::cnstr_set(x_1, 0, x_19);
return x_1;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint32 x_24; uint8 x_25; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_1);
x_24 = lean::unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = lean::unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_21);
x_28 = lean::box_uint32(x_2);
x_29 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_29, 0, x_20);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_29, 2, x_3);
lean::cnstr_set(x_29, 3, x_23);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_23, x_2, x_3);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_21);
lean::cnstr_set(x_31, 2, x_22);
lean::cnstr_set(x_31, 3, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_20, x_2, x_3);
x_33 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_21);
lean::cnstr_set(x_33, 2, x_22);
lean::cnstr_set(x_33, 3, x_23);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_1);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint32 x_39; uint8 x_40; 
x_35 = lean::cnstr_get(x_1, 0);
x_36 = lean::cnstr_get(x_1, 1);
x_37 = lean::cnstr_get(x_1, 2);
x_38 = lean::cnstr_get(x_1, 3);
x_39 = lean::unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = lean::unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
obj* x_43; 
lean::dec(x_37);
lean::dec(x_36);
x_43 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
obj* x_45; 
x_45 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_38, x_2, x_3);
lean::cnstr_set(x_1, 3, x_45);
return x_1;
}
else
{
obj* x_46; 
x_46 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_38, x_2, x_3);
if (lean::obj_tag(x_46) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_35);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; 
x_48 = lean::cnstr_get(x_46, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_46);
if (x_49 == 0)
{
obj* x_50; obj* x_51; uint8 x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_46, 3);
lean::dec(x_50);
x_51 = lean::cnstr_get(x_46, 0);
lean::dec(x_51);
x_52 = 0;
lean::cnstr_set(x_46, 0, x_48);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
obj* x_54; obj* x_55; uint8 x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_46, 1);
x_55 = lean::cnstr_get(x_46, 2);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_46);
x_56 = 0;
x_57 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_57, 0, x_48);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_55);
lean::cnstr_set(x_57, 3, x_48);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean::cnstr_set(x_1, 3, x_57);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8 x_59; 
x_59 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_46);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_61 = lean::cnstr_get(x_46, 1);
x_62 = lean::cnstr_get(x_46, 2);
x_63 = lean::cnstr_get(x_46, 3);
lean::dec(x_63);
x_64 = lean::cnstr_get(x_46, 0);
lean::dec(x_64);
x_65 = !lean::is_exclusive(x_48);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; uint8 x_70; 
x_66 = lean::cnstr_get(x_48, 0);
x_67 = lean::cnstr_get(x_48, 1);
x_68 = lean::cnstr_get(x_48, 2);
x_69 = lean::cnstr_get(x_48, 3);
x_70 = 1;
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set(x_48, 2, x_37);
lean::cnstr_set(x_48, 1, x_36);
lean::cnstr_set(x_48, 0, x_35);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_70);
lean::cnstr_set(x_46, 3, x_69);
lean::cnstr_set(x_46, 2, x_68);
lean::cnstr_set(x_46, 1, x_67);
lean::cnstr_set(x_46, 0, x_66);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_70);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_48);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; uint8 x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_48, 0);
x_72 = lean::cnstr_get(x_48, 1);
x_73 = lean::cnstr_get(x_48, 2);
x_74 = lean::cnstr_get(x_48, 3);
lean::inc(x_74);
lean::inc(x_73);
lean::inc(x_72);
lean::inc(x_71);
lean::dec(x_48);
x_75 = 1;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_35);
lean::cnstr_set(x_76, 1, x_36);
lean::cnstr_set(x_76, 2, x_37);
lean::cnstr_set(x_76, 3, x_47);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_75);
lean::cnstr_set(x_46, 3, x_74);
lean::cnstr_set(x_46, 2, x_73);
lean::cnstr_set(x_46, 1, x_72);
lean::cnstr_set(x_46, 0, x_71);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_75);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_76);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; 
x_77 = lean::cnstr_get(x_46, 1);
x_78 = lean::cnstr_get(x_46, 2);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_48, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_48, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_48, 2);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_48, 3);
lean::inc(x_82);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 lean::cnstr_release(x_48, 2);
 lean::cnstr_release(x_48, 3);
 x_83 = x_48;
} else {
 lean::dec_ref(x_48);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_35);
lean::cnstr_set(x_85, 1, x_36);
lean::cnstr_set(x_85, 2, x_37);
lean::cnstr_set(x_85, 3, x_47);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_79);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_81);
lean::cnstr_set(x_86, 3, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_84);
lean::cnstr_set(x_1, 3, x_86);
lean::cnstr_set(x_1, 2, x_78);
lean::cnstr_set(x_1, 1, x_77);
lean::cnstr_set(x_1, 0, x_85);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_46);
if (x_87 == 0)
{
obj* x_88; obj* x_89; uint8 x_90; 
x_88 = lean::cnstr_get(x_46, 3);
lean::dec(x_88);
x_89 = lean::cnstr_get(x_46, 0);
lean::dec(x_89);
x_90 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_90);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_91; obj* x_92; uint8 x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_46, 1);
x_92 = lean::cnstr_get(x_46, 2);
lean::inc(x_92);
lean::inc(x_91);
lean::dec(x_46);
x_93 = 0;
x_94 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_94, 0, x_47);
lean::cnstr_set(x_94, 1, x_91);
lean::cnstr_set(x_94, 2, x_92);
lean::cnstr_set(x_94, 3, x_48);
lean::cnstr_set_scalar(x_94, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_94);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8 x_95; 
x_95 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8 x_96; 
x_96 = !lean::is_exclusive(x_46);
if (x_96 == 0)
{
obj* x_97; uint8 x_98; 
x_97 = lean::cnstr_get(x_46, 0);
lean::dec(x_97);
x_98 = !lean::is_exclusive(x_47);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; uint8 x_103; 
x_99 = lean::cnstr_get(x_47, 0);
x_100 = lean::cnstr_get(x_47, 1);
x_101 = lean::cnstr_get(x_47, 2);
x_102 = lean::cnstr_get(x_47, 3);
x_103 = 1;
lean::cnstr_set(x_47, 3, x_99);
lean::cnstr_set(x_47, 2, x_37);
lean::cnstr_set(x_47, 1, x_36);
lean::cnstr_set(x_47, 0, x_35);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_103);
lean::cnstr_set(x_46, 0, x_102);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_103);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_101);
lean::cnstr_set(x_1, 1, x_100);
lean::cnstr_set(x_1, 0, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_47, 0);
x_105 = lean::cnstr_get(x_47, 1);
x_106 = lean::cnstr_get(x_47, 2);
x_107 = lean::cnstr_get(x_47, 3);
lean::inc(x_107);
lean::inc(x_106);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_47);
x_108 = 1;
x_109 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_109, 0, x_35);
lean::cnstr_set(x_109, 1, x_36);
lean::cnstr_set(x_109, 2, x_37);
lean::cnstr_set(x_109, 3, x_104);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
lean::cnstr_set(x_46, 0, x_107);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_106);
lean::cnstr_set(x_1, 1, x_105);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; 
x_110 = lean::cnstr_get(x_46, 1);
x_111 = lean::cnstr_get(x_46, 2);
x_112 = lean::cnstr_get(x_46, 3);
lean::inc(x_112);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_46);
x_113 = lean::cnstr_get(x_47, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_47, 1);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_47, 2);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_47, 3);
lean::inc(x_116);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_117 = x_47;
} else {
 lean::dec_ref(x_47);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_35);
lean::cnstr_set(x_119, 1, x_36);
lean::cnstr_set(x_119, 2, x_37);
lean::cnstr_set(x_119, 3, x_113);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set(x_120, 1, x_110);
lean::cnstr_set(x_120, 2, x_111);
lean::cnstr_set(x_120, 3, x_112);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_120);
lean::cnstr_set(x_1, 2, x_115);
lean::cnstr_set(x_1, 1, x_114);
lean::cnstr_set(x_1, 0, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_46, 3);
lean::inc(x_121);
if (lean::obj_tag(x_121) == 0)
{
uint8 x_122; 
x_122 = !lean::is_exclusive(x_46);
if (x_122 == 0)
{
obj* x_123; obj* x_124; uint8 x_125; 
x_123 = lean::cnstr_get(x_46, 3);
lean::dec(x_123);
x_124 = lean::cnstr_get(x_46, 0);
lean::dec(x_124);
x_125 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_125);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_126; obj* x_127; uint8 x_128; obj* x_129; 
x_126 = lean::cnstr_get(x_46, 1);
x_127 = lean::cnstr_get(x_46, 2);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_46);
x_128 = 0;
x_129 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_129, 0, x_47);
lean::cnstr_set(x_129, 1, x_126);
lean::cnstr_set(x_129, 2, x_127);
lean::cnstr_set(x_129, 3, x_121);
lean::cnstr_set_scalar(x_129, sizeof(void*)*4, x_128);
lean::cnstr_set(x_1, 3, x_129);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8 x_130; 
x_130 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8 x_131; 
lean::free_heap_obj(x_1);
x_131 = !lean::is_exclusive(x_46);
if (x_131 == 0)
{
obj* x_132; obj* x_133; uint8 x_134; 
x_132 = lean::cnstr_get(x_46, 3);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_46, 0);
lean::dec(x_133);
x_134 = !lean::is_exclusive(x_121);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; uint8 x_139; 
x_135 = lean::cnstr_get(x_121, 0);
x_136 = lean::cnstr_get(x_121, 1);
x_137 = lean::cnstr_get(x_121, 2);
x_138 = lean::cnstr_get(x_121, 3);
lean::inc(x_47);
lean::cnstr_set(x_121, 3, x_47);
lean::cnstr_set(x_121, 2, x_37);
lean::cnstr_set(x_121, 1, x_36);
lean::cnstr_set(x_121, 0, x_35);
x_139 = !lean::is_exclusive(x_47);
if (x_139 == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_140 = lean::cnstr_get(x_47, 3);
lean::dec(x_140);
x_141 = lean::cnstr_get(x_47, 2);
lean::dec(x_141);
x_142 = lean::cnstr_get(x_47, 1);
lean::dec(x_142);
x_143 = lean::cnstr_get(x_47, 0);
lean::dec(x_143);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
lean::cnstr_set(x_47, 3, x_138);
lean::cnstr_set(x_47, 2, x_137);
lean::cnstr_set(x_47, 1, x_136);
lean::cnstr_set(x_47, 0, x_135);
lean::cnstr_set(x_46, 3, x_47);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
obj* x_144; 
lean::dec(x_47);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
x_144 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_144, 0, x_135);
lean::cnstr_set(x_144, 1, x_136);
lean::cnstr_set(x_144, 2, x_137);
lean::cnstr_set(x_144, 3, x_138);
lean::cnstr_set_scalar(x_144, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_144);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_121, 0);
x_146 = lean::cnstr_get(x_121, 1);
x_147 = lean::cnstr_get(x_121, 2);
x_148 = lean::cnstr_get(x_121, 3);
lean::inc(x_148);
lean::inc(x_147);
lean::inc(x_146);
lean::inc(x_145);
lean::dec(x_121);
lean::inc(x_47);
x_149 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_149, 0, x_35);
lean::cnstr_set(x_149, 1, x_36);
lean::cnstr_set(x_149, 2, x_37);
lean::cnstr_set(x_149, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_150 = x_47;
} else {
 lean::dec_ref(x_47);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_145);
lean::cnstr_set(x_151, 1, x_146);
lean::cnstr_set(x_151, 2, x_147);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_151);
lean::cnstr_set(x_46, 0, x_149);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_152 = lean::cnstr_get(x_46, 1);
x_153 = lean::cnstr_get(x_46, 2);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_46);
x_154 = lean::cnstr_get(x_121, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_121, 1);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_121, 2);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_121, 3);
lean::inc(x_157);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 lean::cnstr_release(x_121, 2);
 lean::cnstr_release(x_121, 3);
 x_158 = x_121;
} else {
 lean::dec_ref(x_121);
 x_158 = lean::box(0);
}
lean::inc(x_47);
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_35);
lean::cnstr_set(x_159, 1, x_36);
lean::cnstr_set(x_159, 2, x_37);
lean::cnstr_set(x_159, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_160 = x_47;
} else {
 lean::dec_ref(x_47);
 x_160 = lean::box(0);
}
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_154);
lean::cnstr_set(x_161, 1, x_155);
lean::cnstr_set(x_161, 2, x_156);
lean::cnstr_set(x_161, 3, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*4, x_95);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_152);
lean::cnstr_set(x_162, 2, x_153);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8 x_163; 
x_163 = !lean::is_exclusive(x_46);
if (x_163 == 0)
{
obj* x_164; obj* x_165; uint8 x_166; 
x_164 = lean::cnstr_get(x_46, 3);
lean::dec(x_164);
x_165 = lean::cnstr_get(x_46, 0);
lean::dec(x_165);
x_166 = !lean::is_exclusive(x_47);
if (x_166 == 0)
{
uint8 x_167; 
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_167);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; uint8 x_173; 
x_168 = lean::cnstr_get(x_47, 0);
x_169 = lean::cnstr_get(x_47, 1);
x_170 = lean::cnstr_get(x_47, 2);
x_171 = lean::cnstr_get(x_47, 3);
lean::inc(x_171);
lean::inc(x_170);
lean::inc(x_169);
lean::inc(x_168);
lean::dec(x_47);
x_172 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set(x_172, 1, x_169);
lean::cnstr_set(x_172, 2, x_170);
lean::cnstr_set(x_172, 3, x_171);
lean::cnstr_set_scalar(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean::cnstr_set(x_46, 0, x_172);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_173);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; 
x_174 = lean::cnstr_get(x_46, 1);
x_175 = lean::cnstr_get(x_46, 2);
lean::inc(x_175);
lean::inc(x_174);
lean::dec(x_46);
x_176 = lean::cnstr_get(x_47, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_47, 1);
lean::inc(x_177);
x_178 = lean::cnstr_get(x_47, 2);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_47, 3);
lean::inc(x_179);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_180 = x_47;
} else {
 lean::dec_ref(x_47);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_176);
lean::cnstr_set(x_181, 1, x_177);
lean::cnstr_set(x_181, 2, x_178);
lean::cnstr_set(x_181, 3, x_179);
lean::cnstr_set_scalar(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_183, 0, x_181);
lean::cnstr_set(x_183, 1, x_174);
lean::cnstr_set(x_183, 2, x_175);
lean::cnstr_set(x_183, 3, x_121);
lean::cnstr_set_scalar(x_183, sizeof(void*)*4, x_182);
lean::cnstr_set(x_1, 3, x_183);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
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
uint8 x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
obj* x_185; 
x_185 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_35, x_2, x_3);
lean::cnstr_set(x_1, 0, x_185);
return x_1;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_35, x_2, x_3);
if (lean::obj_tag(x_186) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_38);
lean::dec(x_37);
lean::dec(x_36);
return x_186;
}
else
{
obj* x_187; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; 
x_188 = lean::cnstr_get(x_186, 3);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
uint8 x_189; 
x_189 = !lean::is_exclusive(x_186);
if (x_189 == 0)
{
obj* x_190; obj* x_191; uint8 x_192; uint8 x_193; 
x_190 = lean::cnstr_get(x_186, 3);
lean::dec(x_190);
x_191 = lean::cnstr_get(x_186, 0);
lean::dec(x_191);
x_192 = 0;
lean::cnstr_set(x_186, 0, x_188);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
obj* x_194; obj* x_195; uint8 x_196; obj* x_197; uint8 x_198; 
x_194 = lean::cnstr_get(x_186, 1);
x_195 = lean::cnstr_get(x_186, 2);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_186);
x_196 = 0;
x_197 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_197, 0, x_188);
lean::cnstr_set(x_197, 1, x_194);
lean::cnstr_set(x_197, 2, x_195);
lean::cnstr_set(x_197, 3, x_188);
lean::cnstr_set_scalar(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean::cnstr_set(x_1, 0, x_197);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8 x_199; 
x_199 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8 x_200; 
x_200 = !lean::is_exclusive(x_186);
if (x_200 == 0)
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; 
x_201 = lean::cnstr_get(x_186, 1);
x_202 = lean::cnstr_get(x_186, 2);
x_203 = lean::cnstr_get(x_186, 3);
lean::dec(x_203);
x_204 = lean::cnstr_get(x_186, 0);
lean::dec(x_204);
x_205 = !lean::is_exclusive(x_188);
if (x_205 == 0)
{
obj* x_206; obj* x_207; obj* x_208; obj* x_209; uint8 x_210; 
x_206 = lean::cnstr_get(x_188, 0);
x_207 = lean::cnstr_get(x_188, 1);
x_208 = lean::cnstr_get(x_188, 2);
x_209 = lean::cnstr_get(x_188, 3);
x_210 = 1;
lean::cnstr_set(x_188, 3, x_206);
lean::cnstr_set(x_188, 2, x_202);
lean::cnstr_set(x_188, 1, x_201);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set_scalar(x_188, sizeof(void*)*4, x_210);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_209);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_210);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_208);
lean::cnstr_set(x_1, 1, x_207);
lean::cnstr_set(x_1, 0, x_188);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; uint8 x_215; obj* x_216; 
x_211 = lean::cnstr_get(x_188, 0);
x_212 = lean::cnstr_get(x_188, 1);
x_213 = lean::cnstr_get(x_188, 2);
x_214 = lean::cnstr_get(x_188, 3);
lean::inc(x_214);
lean::inc(x_213);
lean::inc(x_212);
lean::inc(x_211);
lean::dec(x_188);
x_215 = 1;
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_187);
lean::cnstr_set(x_216, 1, x_201);
lean::cnstr_set(x_216, 2, x_202);
lean::cnstr_set(x_216, 3, x_211);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_215);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_214);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_215);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_213);
lean::cnstr_set(x_1, 1, x_212);
lean::cnstr_set(x_1, 0, x_216);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; uint8 x_224; obj* x_225; obj* x_226; 
x_217 = lean::cnstr_get(x_186, 1);
x_218 = lean::cnstr_get(x_186, 2);
lean::inc(x_218);
lean::inc(x_217);
lean::dec(x_186);
x_219 = lean::cnstr_get(x_188, 0);
lean::inc(x_219);
x_220 = lean::cnstr_get(x_188, 1);
lean::inc(x_220);
x_221 = lean::cnstr_get(x_188, 2);
lean::inc(x_221);
x_222 = lean::cnstr_get(x_188, 3);
lean::inc(x_222);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 lean::cnstr_release(x_188, 2);
 lean::cnstr_release(x_188, 3);
 x_223 = x_188;
} else {
 lean::dec_ref(x_188);
 x_223 = lean::box(0);
}
x_224 = 1;
if (lean::is_scalar(x_223)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_223;
}
lean::cnstr_set(x_225, 0, x_187);
lean::cnstr_set(x_225, 1, x_217);
lean::cnstr_set(x_225, 2, x_218);
lean::cnstr_set(x_225, 3, x_219);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_224);
x_226 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set(x_226, 1, x_36);
lean::cnstr_set(x_226, 2, x_37);
lean::cnstr_set(x_226, 3, x_38);
lean::cnstr_set_scalar(x_226, sizeof(void*)*4, x_224);
lean::cnstr_set(x_1, 3, x_226);
lean::cnstr_set(x_1, 2, x_221);
lean::cnstr_set(x_1, 1, x_220);
lean::cnstr_set(x_1, 0, x_225);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8 x_227; 
x_227 = !lean::is_exclusive(x_186);
if (x_227 == 0)
{
obj* x_228; obj* x_229; uint8 x_230; 
x_228 = lean::cnstr_get(x_186, 3);
lean::dec(x_228);
x_229 = lean::cnstr_get(x_186, 0);
lean::dec(x_229);
x_230 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_230);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_231; obj* x_232; uint8 x_233; obj* x_234; 
x_231 = lean::cnstr_get(x_186, 1);
x_232 = lean::cnstr_get(x_186, 2);
lean::inc(x_232);
lean::inc(x_231);
lean::dec(x_186);
x_233 = 0;
x_234 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_234, 0, x_187);
lean::cnstr_set(x_234, 1, x_231);
lean::cnstr_set(x_234, 2, x_232);
lean::cnstr_set(x_234, 3, x_188);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 0, x_234);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8 x_235; 
x_235 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8 x_236; 
x_236 = !lean::is_exclusive(x_186);
if (x_236 == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; uint8 x_241; 
x_237 = lean::cnstr_get(x_186, 1);
x_238 = lean::cnstr_get(x_186, 2);
x_239 = lean::cnstr_get(x_186, 3);
x_240 = lean::cnstr_get(x_186, 0);
lean::dec(x_240);
x_241 = !lean::is_exclusive(x_187);
if (x_241 == 0)
{
uint8 x_242; 
x_242 = 1;
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_242);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_242);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; 
x_243 = lean::cnstr_get(x_187, 0);
x_244 = lean::cnstr_get(x_187, 1);
x_245 = lean::cnstr_get(x_187, 2);
x_246 = lean::cnstr_get(x_187, 3);
lean::inc(x_246);
lean::inc(x_245);
lean::inc(x_244);
lean::inc(x_243);
lean::dec(x_187);
x_247 = 1;
x_248 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_248, 0, x_243);
lean::cnstr_set(x_248, 1, x_244);
lean::cnstr_set(x_248, 2, x_245);
lean::cnstr_set(x_248, 3, x_246);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; uint8 x_257; obj* x_258; obj* x_259; 
x_249 = lean::cnstr_get(x_186, 1);
x_250 = lean::cnstr_get(x_186, 2);
x_251 = lean::cnstr_get(x_186, 3);
lean::inc(x_251);
lean::inc(x_250);
lean::inc(x_249);
lean::dec(x_186);
x_252 = lean::cnstr_get(x_187, 0);
lean::inc(x_252);
x_253 = lean::cnstr_get(x_187, 1);
lean::inc(x_253);
x_254 = lean::cnstr_get(x_187, 2);
lean::inc(x_254);
x_255 = lean::cnstr_get(x_187, 3);
lean::inc(x_255);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_256 = x_187;
} else {
 lean::dec_ref(x_187);
 x_256 = lean::box(0);
}
x_257 = 1;
if (lean::is_scalar(x_256)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_256;
}
lean::cnstr_set(x_258, 0, x_252);
lean::cnstr_set(x_258, 1, x_253);
lean::cnstr_set(x_258, 2, x_254);
lean::cnstr_set(x_258, 3, x_255);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
x_259 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_259, 0, x_251);
lean::cnstr_set(x_259, 1, x_36);
lean::cnstr_set(x_259, 2, x_37);
lean::cnstr_set(x_259, 3, x_38);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 3, x_259);
lean::cnstr_set(x_1, 2, x_250);
lean::cnstr_set(x_1, 1, x_249);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_186, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
uint8 x_261; 
x_261 = !lean::is_exclusive(x_186);
if (x_261 == 0)
{
obj* x_262; obj* x_263; uint8 x_264; 
x_262 = lean::cnstr_get(x_186, 3);
lean::dec(x_262);
x_263 = lean::cnstr_get(x_186, 0);
lean::dec(x_263);
x_264 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_264);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_265; obj* x_266; uint8 x_267; obj* x_268; 
x_265 = lean::cnstr_get(x_186, 1);
x_266 = lean::cnstr_get(x_186, 2);
lean::inc(x_266);
lean::inc(x_265);
lean::dec(x_186);
x_267 = 0;
x_268 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_268, 0, x_187);
lean::cnstr_set(x_268, 1, x_265);
lean::cnstr_set(x_268, 2, x_266);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
lean::cnstr_set(x_1, 0, x_268);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8 x_269; 
x_269 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8 x_270; 
lean::free_heap_obj(x_1);
x_270 = !lean::is_exclusive(x_186);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; uint8 x_275; 
x_271 = lean::cnstr_get(x_186, 1);
x_272 = lean::cnstr_get(x_186, 2);
x_273 = lean::cnstr_get(x_186, 3);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_186, 0);
lean::dec(x_274);
x_275 = !lean::is_exclusive(x_260);
if (x_275 == 0)
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; uint8 x_280; 
x_276 = lean::cnstr_get(x_260, 0);
x_277 = lean::cnstr_get(x_260, 1);
x_278 = lean::cnstr_get(x_260, 2);
x_279 = lean::cnstr_get(x_260, 3);
lean::inc(x_187);
lean::cnstr_set(x_260, 3, x_276);
lean::cnstr_set(x_260, 2, x_272);
lean::cnstr_set(x_260, 1, x_271);
lean::cnstr_set(x_260, 0, x_187);
x_280 = !lean::is_exclusive(x_187);
if (x_280 == 0)
{
obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_281 = lean::cnstr_get(x_187, 3);
lean::dec(x_281);
x_282 = lean::cnstr_get(x_187, 2);
lean::dec(x_282);
x_283 = lean::cnstr_get(x_187, 1);
lean::dec(x_283);
x_284 = lean::cnstr_get(x_187, 0);
lean::dec(x_284);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
lean::cnstr_set(x_187, 3, x_38);
lean::cnstr_set(x_187, 2, x_37);
lean::cnstr_set(x_187, 1, x_36);
lean::cnstr_set(x_187, 0, x_279);
lean::cnstr_set(x_186, 3, x_187);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
obj* x_285; 
lean::dec(x_187);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
x_285 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_285, 0, x_279);
lean::cnstr_set(x_285, 1, x_36);
lean::cnstr_set(x_285, 2, x_37);
lean::cnstr_set(x_285, 3, x_38);
lean::cnstr_set_scalar(x_285, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_285);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
x_286 = lean::cnstr_get(x_260, 0);
x_287 = lean::cnstr_get(x_260, 1);
x_288 = lean::cnstr_get(x_260, 2);
x_289 = lean::cnstr_get(x_260, 3);
lean::inc(x_289);
lean::inc(x_288);
lean::inc(x_287);
lean::inc(x_286);
lean::dec(x_260);
lean::inc(x_187);
x_290 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_290, 0, x_187);
lean::cnstr_set(x_290, 1, x_271);
lean::cnstr_set(x_290, 2, x_272);
lean::cnstr_set(x_290, 3, x_286);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_291 = x_187;
} else {
 lean::dec_ref(x_187);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_289);
lean::cnstr_set(x_292, 1, x_36);
lean::cnstr_set(x_292, 2, x_37);
lean::cnstr_set(x_292, 3, x_38);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_292);
lean::cnstr_set(x_186, 2, x_288);
lean::cnstr_set(x_186, 1, x_287);
lean::cnstr_set(x_186, 0, x_290);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_293 = lean::cnstr_get(x_186, 1);
x_294 = lean::cnstr_get(x_186, 2);
lean::inc(x_294);
lean::inc(x_293);
lean::dec(x_186);
x_295 = lean::cnstr_get(x_260, 0);
lean::inc(x_295);
x_296 = lean::cnstr_get(x_260, 1);
lean::inc(x_296);
x_297 = lean::cnstr_get(x_260, 2);
lean::inc(x_297);
x_298 = lean::cnstr_get(x_260, 3);
lean::inc(x_298);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 lean::cnstr_release(x_260, 2);
 lean::cnstr_release(x_260, 3);
 x_299 = x_260;
} else {
 lean::dec_ref(x_260);
 x_299 = lean::box(0);
}
lean::inc(x_187);
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_187);
lean::cnstr_set(x_300, 1, x_293);
lean::cnstr_set(x_300, 2, x_294);
lean::cnstr_set(x_300, 3, x_295);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_301 = x_187;
} else {
 lean::dec_ref(x_187);
 x_301 = lean::box(0);
}
lean::cnstr_set_scalar(x_300, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_301)) {
 x_302 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_302 = x_301;
}
lean::cnstr_set(x_302, 0, x_298);
lean::cnstr_set(x_302, 1, x_36);
lean::cnstr_set(x_302, 2, x_37);
lean::cnstr_set(x_302, 3, x_38);
lean::cnstr_set_scalar(x_302, sizeof(void*)*4, x_235);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_296);
lean::cnstr_set(x_303, 2, x_297);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8 x_304; 
x_304 = !lean::is_exclusive(x_186);
if (x_304 == 0)
{
obj* x_305; obj* x_306; uint8 x_307; 
x_305 = lean::cnstr_get(x_186, 3);
lean::dec(x_305);
x_306 = lean::cnstr_get(x_186, 0);
lean::dec(x_306);
x_307 = !lean::is_exclusive(x_187);
if (x_307 == 0)
{
uint8 x_308; 
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_308);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; uint8 x_314; 
x_309 = lean::cnstr_get(x_187, 0);
x_310 = lean::cnstr_get(x_187, 1);
x_311 = lean::cnstr_get(x_187, 2);
x_312 = lean::cnstr_get(x_187, 3);
lean::inc(x_312);
lean::inc(x_311);
lean::inc(x_310);
lean::inc(x_309);
lean::dec(x_187);
x_313 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_313, 0, x_309);
lean::cnstr_set(x_313, 1, x_310);
lean::cnstr_set(x_313, 2, x_311);
lean::cnstr_set(x_313, 3, x_312);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean::cnstr_set(x_186, 0, x_313);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_314);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; uint8 x_323; obj* x_324; 
x_315 = lean::cnstr_get(x_186, 1);
x_316 = lean::cnstr_get(x_186, 2);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_186);
x_317 = lean::cnstr_get(x_187, 0);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_187, 1);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_187, 2);
lean::inc(x_319);
x_320 = lean::cnstr_get(x_187, 3);
lean::inc(x_320);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_321 = x_187;
} else {
 lean::dec_ref(x_187);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_317);
lean::cnstr_set(x_322, 1, x_318);
lean::cnstr_set(x_322, 2, x_319);
lean::cnstr_set(x_322, 3, x_320);
lean::cnstr_set_scalar(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_322);
lean::cnstr_set(x_324, 1, x_315);
lean::cnstr_set(x_324, 2, x_316);
lean::cnstr_set(x_324, 3, x_260);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_323);
lean::cnstr_set(x_1, 0, x_324);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
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
obj* x_325; obj* x_326; obj* x_327; obj* x_328; uint32 x_329; uint8 x_330; 
x_325 = lean::cnstr_get(x_1, 0);
x_326 = lean::cnstr_get(x_1, 1);
x_327 = lean::cnstr_get(x_1, 2);
x_328 = lean::cnstr_get(x_1, 3);
lean::inc(x_328);
lean::inc(x_327);
lean::inc(x_326);
lean::inc(x_325);
lean::dec(x_1);
x_329 = lean::unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32 x_331; uint8 x_332; 
x_331 = lean::unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
obj* x_333; obj* x_334; 
lean::dec(x_327);
lean::dec(x_326);
x_333 = lean::box_uint32(x_2);
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_325);
lean::cnstr_set(x_334, 1, x_333);
lean::cnstr_set(x_334, 2, x_3);
lean::cnstr_set(x_334, 3, x_328);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8 x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
obj* x_336; obj* x_337; 
x_336 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_328, x_2, x_3);
x_337 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_337, 0, x_325);
lean::cnstr_set(x_337, 1, x_326);
lean::cnstr_set(x_337, 2, x_327);
lean::cnstr_set(x_337, 3, x_336);
lean::cnstr_set_scalar(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
obj* x_338; 
x_338 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_328, x_2, x_3);
if (lean::obj_tag(x_338) == 0)
{
lean::dec(x_327);
lean::dec(x_326);
lean::dec(x_325);
return x_338;
}
else
{
obj* x_339; 
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
if (lean::obj_tag(x_339) == 0)
{
obj* x_340; 
x_340 = lean::cnstr_get(x_338, 3);
lean::inc(x_340);
if (lean::obj_tag(x_340) == 0)
{
obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; uint8 x_346; obj* x_347; 
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_338, 2);
lean::inc(x_342);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_343 = x_338;
} else {
 lean::dec_ref(x_338);
 x_343 = lean::box(0);
}
x_344 = 0;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_340);
lean::cnstr_set(x_345, 1, x_341);
lean::cnstr_set(x_345, 2, x_342);
lean::cnstr_set(x_345, 3, x_340);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_325);
lean::cnstr_set(x_347, 1, x_326);
lean::cnstr_set(x_347, 2, x_327);
lean::cnstr_set(x_347, 3, x_345);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8 x_348; 
x_348 = lean::cnstr_get_scalar<uint8>(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; uint8 x_357; obj* x_358; obj* x_359; obj* x_360; 
x_349 = lean::cnstr_get(x_338, 1);
lean::inc(x_349);
x_350 = lean::cnstr_get(x_338, 2);
lean::inc(x_350);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_351 = x_338;
} else {
 lean::dec_ref(x_338);
 x_351 = lean::box(0);
}
x_352 = lean::cnstr_get(x_340, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_340, 1);
lean::inc(x_353);
x_354 = lean::cnstr_get(x_340, 2);
lean::inc(x_354);
x_355 = lean::cnstr_get(x_340, 3);
lean::inc(x_355);
if (lean::is_exclusive(x_340)) {
 lean::cnstr_release(x_340, 0);
 lean::cnstr_release(x_340, 1);
 lean::cnstr_release(x_340, 2);
 lean::cnstr_release(x_340, 3);
 x_356 = x_340;
} else {
 lean::dec_ref(x_340);
 x_356 = lean::box(0);
}
x_357 = 1;
if (lean::is_scalar(x_356)) {
 x_358 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_358 = x_356;
}
lean::cnstr_set(x_358, 0, x_325);
lean::cnstr_set(x_358, 1, x_326);
lean::cnstr_set(x_358, 2, x_327);
lean::cnstr_set(x_358, 3, x_339);
lean::cnstr_set_scalar(x_358, sizeof(void*)*4, x_357);
if (lean::is_scalar(x_351)) {
 x_359 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_359 = x_351;
}
lean::cnstr_set(x_359, 0, x_352);
lean::cnstr_set(x_359, 1, x_353);
lean::cnstr_set(x_359, 2, x_354);
lean::cnstr_set(x_359, 3, x_355);
lean::cnstr_set_scalar(x_359, sizeof(void*)*4, x_357);
x_360 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_360, 0, x_358);
lean::cnstr_set(x_360, 1, x_349);
lean::cnstr_set(x_360, 2, x_350);
lean::cnstr_set(x_360, 3, x_359);
lean::cnstr_set_scalar(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; 
x_361 = lean::cnstr_get(x_338, 1);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_338, 2);
lean::inc(x_362);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_363 = x_338;
} else {
 lean::dec_ref(x_338);
 x_363 = lean::box(0);
}
x_364 = 0;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_339);
lean::cnstr_set(x_365, 1, x_361);
lean::cnstr_set(x_365, 2, x_362);
lean::cnstr_set(x_365, 3, x_340);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
x_366 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_366, 0, x_325);
lean::cnstr_set(x_366, 1, x_326);
lean::cnstr_set(x_366, 2, x_327);
lean::cnstr_set(x_366, 3, x_365);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8 x_367; 
x_367 = lean::cnstr_get_scalar<uint8>(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; uint8 x_377; obj* x_378; obj* x_379; obj* x_380; 
x_368 = lean::cnstr_get(x_338, 1);
lean::inc(x_368);
x_369 = lean::cnstr_get(x_338, 2);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_338, 3);
lean::inc(x_370);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_371 = x_338;
} else {
 lean::dec_ref(x_338);
 x_371 = lean::box(0);
}
x_372 = lean::cnstr_get(x_339, 0);
lean::inc(x_372);
x_373 = lean::cnstr_get(x_339, 1);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_339, 2);
lean::inc(x_374);
x_375 = lean::cnstr_get(x_339, 3);
lean::inc(x_375);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_376 = x_339;
} else {
 lean::dec_ref(x_339);
 x_376 = lean::box(0);
}
x_377 = 1;
if (lean::is_scalar(x_376)) {
 x_378 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_378 = x_376;
}
lean::cnstr_set(x_378, 0, x_325);
lean::cnstr_set(x_378, 1, x_326);
lean::cnstr_set(x_378, 2, x_327);
lean::cnstr_set(x_378, 3, x_372);
lean::cnstr_set_scalar(x_378, sizeof(void*)*4, x_377);
if (lean::is_scalar(x_371)) {
 x_379 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_379 = x_371;
}
lean::cnstr_set(x_379, 0, x_375);
lean::cnstr_set(x_379, 1, x_368);
lean::cnstr_set(x_379, 2, x_369);
lean::cnstr_set(x_379, 3, x_370);
lean::cnstr_set_scalar(x_379, sizeof(void*)*4, x_377);
x_380 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_380, 0, x_378);
lean::cnstr_set(x_380, 1, x_373);
lean::cnstr_set(x_380, 2, x_374);
lean::cnstr_set(x_380, 3, x_379);
lean::cnstr_set_scalar(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
obj* x_381; 
x_381 = lean::cnstr_get(x_338, 3);
lean::inc(x_381);
if (lean::obj_tag(x_381) == 0)
{
obj* x_382; obj* x_383; obj* x_384; uint8 x_385; obj* x_386; obj* x_387; 
x_382 = lean::cnstr_get(x_338, 1);
lean::inc(x_382);
x_383 = lean::cnstr_get(x_338, 2);
lean::inc(x_383);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_384 = x_338;
} else {
 lean::dec_ref(x_338);
 x_384 = lean::box(0);
}
x_385 = 0;
if (lean::is_scalar(x_384)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_384;
}
lean::cnstr_set(x_386, 0, x_339);
lean::cnstr_set(x_386, 1, x_382);
lean::cnstr_set(x_386, 2, x_383);
lean::cnstr_set(x_386, 3, x_381);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_385);
x_387 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_387, 0, x_325);
lean::cnstr_set(x_387, 1, x_326);
lean::cnstr_set(x_387, 2, x_327);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8 x_388; 
x_388 = lean::cnstr_get_scalar<uint8>(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; 
x_389 = lean::cnstr_get(x_338, 1);
lean::inc(x_389);
x_390 = lean::cnstr_get(x_338, 2);
lean::inc(x_390);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_391 = x_338;
} else {
 lean::dec_ref(x_338);
 x_391 = lean::box(0);
}
x_392 = lean::cnstr_get(x_381, 0);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_381, 1);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_381, 2);
lean::inc(x_394);
x_395 = lean::cnstr_get(x_381, 3);
lean::inc(x_395);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 lean::cnstr_release(x_381, 1);
 lean::cnstr_release(x_381, 2);
 lean::cnstr_release(x_381, 3);
 x_396 = x_381;
} else {
 lean::dec_ref(x_381);
 x_396 = lean::box(0);
}
lean::inc(x_339);
if (lean::is_scalar(x_396)) {
 x_397 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_397 = x_396;
}
lean::cnstr_set(x_397, 0, x_325);
lean::cnstr_set(x_397, 1, x_326);
lean::cnstr_set(x_397, 2, x_327);
lean::cnstr_set(x_397, 3, x_339);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_398 = x_339;
} else {
 lean::dec_ref(x_339);
 x_398 = lean::box(0);
}
lean::cnstr_set_scalar(x_397, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_392);
lean::cnstr_set(x_399, 1, x_393);
lean::cnstr_set(x_399, 2, x_394);
lean::cnstr_set(x_399, 3, x_395);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_391)) {
 x_400 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_400 = x_391;
}
lean::cnstr_set(x_400, 0, x_397);
lean::cnstr_set(x_400, 1, x_389);
lean::cnstr_set(x_400, 2, x_390);
lean::cnstr_set(x_400, 3, x_399);
lean::cnstr_set_scalar(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; uint8 x_410; obj* x_411; obj* x_412; 
x_401 = lean::cnstr_get(x_338, 1);
lean::inc(x_401);
x_402 = lean::cnstr_get(x_338, 2);
lean::inc(x_402);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_403 = x_338;
} else {
 lean::dec_ref(x_338);
 x_403 = lean::box(0);
}
x_404 = lean::cnstr_get(x_339, 0);
lean::inc(x_404);
x_405 = lean::cnstr_get(x_339, 1);
lean::inc(x_405);
x_406 = lean::cnstr_get(x_339, 2);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_339, 3);
lean::inc(x_407);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_408 = x_339;
} else {
 lean::dec_ref(x_339);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_404);
lean::cnstr_set(x_409, 1, x_405);
lean::cnstr_set(x_409, 2, x_406);
lean::cnstr_set(x_409, 3, x_407);
lean::cnstr_set_scalar(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean::is_scalar(x_403)) {
 x_411 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_411 = x_403;
}
lean::cnstr_set(x_411, 0, x_409);
lean::cnstr_set(x_411, 1, x_401);
lean::cnstr_set(x_411, 2, x_402);
lean::cnstr_set(x_411, 3, x_381);
lean::cnstr_set_scalar(x_411, sizeof(void*)*4, x_410);
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_325);
lean::cnstr_set(x_412, 1, x_326);
lean::cnstr_set(x_412, 2, x_327);
lean::cnstr_set(x_412, 3, x_411);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_388);
return x_412;
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
uint8 x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
obj* x_414; obj* x_415; 
x_414 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_325, x_2, x_3);
x_415 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_415, 0, x_414);
lean::cnstr_set(x_415, 1, x_326);
lean::cnstr_set(x_415, 2, x_327);
lean::cnstr_set(x_415, 3, x_328);
lean::cnstr_set_scalar(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
obj* x_416; 
x_416 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_325, x_2, x_3);
if (lean::obj_tag(x_416) == 0)
{
lean::dec(x_328);
lean::dec(x_327);
lean::dec(x_326);
return x_416;
}
else
{
obj* x_417; 
x_417 = lean::cnstr_get(x_416, 0);
lean::inc(x_417);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; 
x_418 = lean::cnstr_get(x_416, 3);
lean::inc(x_418);
if (lean::obj_tag(x_418) == 0)
{
obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; uint8 x_424; obj* x_425; 
x_419 = lean::cnstr_get(x_416, 1);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_416, 2);
lean::inc(x_420);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_421 = x_416;
} else {
 lean::dec_ref(x_416);
 x_421 = lean::box(0);
}
x_422 = 0;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_418);
lean::cnstr_set(x_423, 1, x_419);
lean::cnstr_set(x_423, 2, x_420);
lean::cnstr_set(x_423, 3, x_418);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_326);
lean::cnstr_set(x_425, 2, x_327);
lean::cnstr_set(x_425, 3, x_328);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8 x_426; 
x_426 = lean::cnstr_get_scalar<uint8>(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; uint8 x_435; obj* x_436; obj* x_437; obj* x_438; 
x_427 = lean::cnstr_get(x_416, 1);
lean::inc(x_427);
x_428 = lean::cnstr_get(x_416, 2);
lean::inc(x_428);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_429 = x_416;
} else {
 lean::dec_ref(x_416);
 x_429 = lean::box(0);
}
x_430 = lean::cnstr_get(x_418, 0);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_418, 1);
lean::inc(x_431);
x_432 = lean::cnstr_get(x_418, 2);
lean::inc(x_432);
x_433 = lean::cnstr_get(x_418, 3);
lean::inc(x_433);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 lean::cnstr_release(x_418, 2);
 lean::cnstr_release(x_418, 3);
 x_434 = x_418;
} else {
 lean::dec_ref(x_418);
 x_434 = lean::box(0);
}
x_435 = 1;
if (lean::is_scalar(x_434)) {
 x_436 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_436 = x_434;
}
lean::cnstr_set(x_436, 0, x_417);
lean::cnstr_set(x_436, 1, x_427);
lean::cnstr_set(x_436, 2, x_428);
lean::cnstr_set(x_436, 3, x_430);
lean::cnstr_set_scalar(x_436, sizeof(void*)*4, x_435);
if (lean::is_scalar(x_429)) {
 x_437 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_437 = x_429;
}
lean::cnstr_set(x_437, 0, x_433);
lean::cnstr_set(x_437, 1, x_326);
lean::cnstr_set(x_437, 2, x_327);
lean::cnstr_set(x_437, 3, x_328);
lean::cnstr_set_scalar(x_437, sizeof(void*)*4, x_435);
x_438 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_438, 0, x_436);
lean::cnstr_set(x_438, 1, x_431);
lean::cnstr_set(x_438, 2, x_432);
lean::cnstr_set(x_438, 3, x_437);
lean::cnstr_set_scalar(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; 
x_439 = lean::cnstr_get(x_416, 1);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_416, 2);
lean::inc(x_440);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_441 = x_416;
} else {
 lean::dec_ref(x_416);
 x_441 = lean::box(0);
}
x_442 = 0;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_417);
lean::cnstr_set(x_443, 1, x_439);
lean::cnstr_set(x_443, 2, x_440);
lean::cnstr_set(x_443, 3, x_418);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
x_444 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_444, 0, x_443);
lean::cnstr_set(x_444, 1, x_326);
lean::cnstr_set(x_444, 2, x_327);
lean::cnstr_set(x_444, 3, x_328);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8 x_445; 
x_445 = lean::cnstr_get_scalar<uint8>(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; 
x_446 = lean::cnstr_get(x_416, 1);
lean::inc(x_446);
x_447 = lean::cnstr_get(x_416, 2);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_416, 3);
lean::inc(x_448);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_449 = x_416;
} else {
 lean::dec_ref(x_416);
 x_449 = lean::box(0);
}
x_450 = lean::cnstr_get(x_417, 0);
lean::inc(x_450);
x_451 = lean::cnstr_get(x_417, 1);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_417, 2);
lean::inc(x_452);
x_453 = lean::cnstr_get(x_417, 3);
lean::inc(x_453);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_454 = x_417;
} else {
 lean::dec_ref(x_417);
 x_454 = lean::box(0);
}
x_455 = 1;
if (lean::is_scalar(x_454)) {
 x_456 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_456 = x_454;
}
lean::cnstr_set(x_456, 0, x_450);
lean::cnstr_set(x_456, 1, x_451);
lean::cnstr_set(x_456, 2, x_452);
lean::cnstr_set(x_456, 3, x_453);
lean::cnstr_set_scalar(x_456, sizeof(void*)*4, x_455);
if (lean::is_scalar(x_449)) {
 x_457 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_457 = x_449;
}
lean::cnstr_set(x_457, 0, x_448);
lean::cnstr_set(x_457, 1, x_326);
lean::cnstr_set(x_457, 2, x_327);
lean::cnstr_set(x_457, 3, x_328);
lean::cnstr_set_scalar(x_457, sizeof(void*)*4, x_455);
x_458 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_458, 0, x_456);
lean::cnstr_set(x_458, 1, x_446);
lean::cnstr_set(x_458, 2, x_447);
lean::cnstr_set(x_458, 3, x_457);
lean::cnstr_set_scalar(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
obj* x_459; 
x_459 = lean::cnstr_get(x_416, 3);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_460; obj* x_461; obj* x_462; uint8 x_463; obj* x_464; obj* x_465; 
x_460 = lean::cnstr_get(x_416, 1);
lean::inc(x_460);
x_461 = lean::cnstr_get(x_416, 2);
lean::inc(x_461);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_462 = x_416;
} else {
 lean::dec_ref(x_416);
 x_462 = lean::box(0);
}
x_463 = 0;
if (lean::is_scalar(x_462)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_462;
}
lean::cnstr_set(x_464, 0, x_417);
lean::cnstr_set(x_464, 1, x_460);
lean::cnstr_set(x_464, 2, x_461);
lean::cnstr_set(x_464, 3, x_459);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_463);
x_465 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_326);
lean::cnstr_set(x_465, 2, x_327);
lean::cnstr_set(x_465, 3, x_328);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8 x_466; 
x_466 = lean::cnstr_get_scalar<uint8>(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; 
x_467 = lean::cnstr_get(x_416, 1);
lean::inc(x_467);
x_468 = lean::cnstr_get(x_416, 2);
lean::inc(x_468);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_469 = x_416;
} else {
 lean::dec_ref(x_416);
 x_469 = lean::box(0);
}
x_470 = lean::cnstr_get(x_459, 0);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_459, 1);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_459, 2);
lean::inc(x_472);
x_473 = lean::cnstr_get(x_459, 3);
lean::inc(x_473);
if (lean::is_exclusive(x_459)) {
 lean::cnstr_release(x_459, 0);
 lean::cnstr_release(x_459, 1);
 lean::cnstr_release(x_459, 2);
 lean::cnstr_release(x_459, 3);
 x_474 = x_459;
} else {
 lean::dec_ref(x_459);
 x_474 = lean::box(0);
}
lean::inc(x_417);
if (lean::is_scalar(x_474)) {
 x_475 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_475 = x_474;
}
lean::cnstr_set(x_475, 0, x_417);
lean::cnstr_set(x_475, 1, x_467);
lean::cnstr_set(x_475, 2, x_468);
lean::cnstr_set(x_475, 3, x_470);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_476 = x_417;
} else {
 lean::dec_ref(x_417);
 x_476 = lean::box(0);
}
lean::cnstr_set_scalar(x_475, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_476)) {
 x_477 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_477 = x_476;
}
lean::cnstr_set(x_477, 0, x_473);
lean::cnstr_set(x_477, 1, x_326);
lean::cnstr_set(x_477, 2, x_327);
lean::cnstr_set(x_477, 3, x_328);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_469)) {
 x_478 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_478 = x_469;
}
lean::cnstr_set(x_478, 0, x_475);
lean::cnstr_set(x_478, 1, x_471);
lean::cnstr_set(x_478, 2, x_472);
lean::cnstr_set(x_478, 3, x_477);
lean::cnstr_set_scalar(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; uint8 x_488; obj* x_489; obj* x_490; 
x_479 = lean::cnstr_get(x_416, 1);
lean::inc(x_479);
x_480 = lean::cnstr_get(x_416, 2);
lean::inc(x_480);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_481 = x_416;
} else {
 lean::dec_ref(x_416);
 x_481 = lean::box(0);
}
x_482 = lean::cnstr_get(x_417, 0);
lean::inc(x_482);
x_483 = lean::cnstr_get(x_417, 1);
lean::inc(x_483);
x_484 = lean::cnstr_get(x_417, 2);
lean::inc(x_484);
x_485 = lean::cnstr_get(x_417, 3);
lean::inc(x_485);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_486 = x_417;
} else {
 lean::dec_ref(x_417);
 x_486 = lean::box(0);
}
if (lean::is_scalar(x_486)) {
 x_487 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_487 = x_486;
}
lean::cnstr_set(x_487, 0, x_482);
lean::cnstr_set(x_487, 1, x_483);
lean::cnstr_set(x_487, 2, x_484);
lean::cnstr_set(x_487, 3, x_485);
lean::cnstr_set_scalar(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean::is_scalar(x_481)) {
 x_489 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_489 = x_481;
}
lean::cnstr_set(x_489, 0, x_487);
lean::cnstr_set(x_489, 1, x_479);
lean::cnstr_set(x_489, 2, x_480);
lean::cnstr_set(x_489, 3, x_459);
lean::cnstr_set_scalar(x_489, sizeof(void*)*4, x_488);
x_490 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_490, 0, x_489);
lean::cnstr_set(x_490, 1, x_326);
lean::cnstr_set(x_490, 2, x_327);
lean::cnstr_set(x_490, 3, x_328);
lean::cnstr_set_scalar(x_490, sizeof(void*)*4, x_466);
return x_490;
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
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::box_uint32(x_2);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
x_13 = lean::unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = lean::unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_17);
return x_1;
}
else
{
obj* x_18; 
x_18 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_12, x_2, x_3);
lean::cnstr_set(x_1, 3, x_18);
return x_1;
}
}
else
{
obj* x_19; 
x_19 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_9, x_2, x_3);
lean::cnstr_set(x_1, 0, x_19);
return x_1;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint32 x_24; uint8 x_25; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_1);
x_24 = lean::unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = lean::unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_21);
x_28 = lean::box_uint32(x_2);
x_29 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_29, 0, x_20);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_29, 2, x_3);
lean::cnstr_set(x_29, 3, x_23);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_23, x_2, x_3);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_21);
lean::cnstr_set(x_31, 2, x_22);
lean::cnstr_set(x_31, 3, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_20, x_2, x_3);
x_33 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_21);
lean::cnstr_set(x_33, 2, x_22);
lean::cnstr_set(x_33, 3, x_23);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_1);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint32 x_39; uint8 x_40; 
x_35 = lean::cnstr_get(x_1, 0);
x_36 = lean::cnstr_get(x_1, 1);
x_37 = lean::cnstr_get(x_1, 2);
x_38 = lean::cnstr_get(x_1, 3);
x_39 = lean::unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = lean::unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
obj* x_43; 
lean::dec(x_37);
lean::dec(x_36);
x_43 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
obj* x_45; 
x_45 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_38, x_2, x_3);
lean::cnstr_set(x_1, 3, x_45);
return x_1;
}
else
{
obj* x_46; 
x_46 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_38, x_2, x_3);
if (lean::obj_tag(x_46) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_35);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; 
x_48 = lean::cnstr_get(x_46, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_46);
if (x_49 == 0)
{
obj* x_50; obj* x_51; uint8 x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_46, 3);
lean::dec(x_50);
x_51 = lean::cnstr_get(x_46, 0);
lean::dec(x_51);
x_52 = 0;
lean::cnstr_set(x_46, 0, x_48);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
obj* x_54; obj* x_55; uint8 x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_46, 1);
x_55 = lean::cnstr_get(x_46, 2);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_46);
x_56 = 0;
x_57 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_57, 0, x_48);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_55);
lean::cnstr_set(x_57, 3, x_48);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean::cnstr_set(x_1, 3, x_57);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8 x_59; 
x_59 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_46);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_61 = lean::cnstr_get(x_46, 1);
x_62 = lean::cnstr_get(x_46, 2);
x_63 = lean::cnstr_get(x_46, 3);
lean::dec(x_63);
x_64 = lean::cnstr_get(x_46, 0);
lean::dec(x_64);
x_65 = !lean::is_exclusive(x_48);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; uint8 x_70; 
x_66 = lean::cnstr_get(x_48, 0);
x_67 = lean::cnstr_get(x_48, 1);
x_68 = lean::cnstr_get(x_48, 2);
x_69 = lean::cnstr_get(x_48, 3);
x_70 = 1;
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set(x_48, 2, x_37);
lean::cnstr_set(x_48, 1, x_36);
lean::cnstr_set(x_48, 0, x_35);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_70);
lean::cnstr_set(x_46, 3, x_69);
lean::cnstr_set(x_46, 2, x_68);
lean::cnstr_set(x_46, 1, x_67);
lean::cnstr_set(x_46, 0, x_66);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_70);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_48);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; uint8 x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_48, 0);
x_72 = lean::cnstr_get(x_48, 1);
x_73 = lean::cnstr_get(x_48, 2);
x_74 = lean::cnstr_get(x_48, 3);
lean::inc(x_74);
lean::inc(x_73);
lean::inc(x_72);
lean::inc(x_71);
lean::dec(x_48);
x_75 = 1;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_35);
lean::cnstr_set(x_76, 1, x_36);
lean::cnstr_set(x_76, 2, x_37);
lean::cnstr_set(x_76, 3, x_47);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_75);
lean::cnstr_set(x_46, 3, x_74);
lean::cnstr_set(x_46, 2, x_73);
lean::cnstr_set(x_46, 1, x_72);
lean::cnstr_set(x_46, 0, x_71);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_75);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_76);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; 
x_77 = lean::cnstr_get(x_46, 1);
x_78 = lean::cnstr_get(x_46, 2);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_48, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_48, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_48, 2);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_48, 3);
lean::inc(x_82);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 lean::cnstr_release(x_48, 2);
 lean::cnstr_release(x_48, 3);
 x_83 = x_48;
} else {
 lean::dec_ref(x_48);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_35);
lean::cnstr_set(x_85, 1, x_36);
lean::cnstr_set(x_85, 2, x_37);
lean::cnstr_set(x_85, 3, x_47);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_79);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_81);
lean::cnstr_set(x_86, 3, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_84);
lean::cnstr_set(x_1, 3, x_86);
lean::cnstr_set(x_1, 2, x_78);
lean::cnstr_set(x_1, 1, x_77);
lean::cnstr_set(x_1, 0, x_85);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_46);
if (x_87 == 0)
{
obj* x_88; obj* x_89; uint8 x_90; 
x_88 = lean::cnstr_get(x_46, 3);
lean::dec(x_88);
x_89 = lean::cnstr_get(x_46, 0);
lean::dec(x_89);
x_90 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_90);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_91; obj* x_92; uint8 x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_46, 1);
x_92 = lean::cnstr_get(x_46, 2);
lean::inc(x_92);
lean::inc(x_91);
lean::dec(x_46);
x_93 = 0;
x_94 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_94, 0, x_47);
lean::cnstr_set(x_94, 1, x_91);
lean::cnstr_set(x_94, 2, x_92);
lean::cnstr_set(x_94, 3, x_48);
lean::cnstr_set_scalar(x_94, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_94);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8 x_95; 
x_95 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8 x_96; 
x_96 = !lean::is_exclusive(x_46);
if (x_96 == 0)
{
obj* x_97; uint8 x_98; 
x_97 = lean::cnstr_get(x_46, 0);
lean::dec(x_97);
x_98 = !lean::is_exclusive(x_47);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; uint8 x_103; 
x_99 = lean::cnstr_get(x_47, 0);
x_100 = lean::cnstr_get(x_47, 1);
x_101 = lean::cnstr_get(x_47, 2);
x_102 = lean::cnstr_get(x_47, 3);
x_103 = 1;
lean::cnstr_set(x_47, 3, x_99);
lean::cnstr_set(x_47, 2, x_37);
lean::cnstr_set(x_47, 1, x_36);
lean::cnstr_set(x_47, 0, x_35);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_103);
lean::cnstr_set(x_46, 0, x_102);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_103);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_101);
lean::cnstr_set(x_1, 1, x_100);
lean::cnstr_set(x_1, 0, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_47, 0);
x_105 = lean::cnstr_get(x_47, 1);
x_106 = lean::cnstr_get(x_47, 2);
x_107 = lean::cnstr_get(x_47, 3);
lean::inc(x_107);
lean::inc(x_106);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_47);
x_108 = 1;
x_109 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_109, 0, x_35);
lean::cnstr_set(x_109, 1, x_36);
lean::cnstr_set(x_109, 2, x_37);
lean::cnstr_set(x_109, 3, x_104);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
lean::cnstr_set(x_46, 0, x_107);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_106);
lean::cnstr_set(x_1, 1, x_105);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; 
x_110 = lean::cnstr_get(x_46, 1);
x_111 = lean::cnstr_get(x_46, 2);
x_112 = lean::cnstr_get(x_46, 3);
lean::inc(x_112);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_46);
x_113 = lean::cnstr_get(x_47, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_47, 1);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_47, 2);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_47, 3);
lean::inc(x_116);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_117 = x_47;
} else {
 lean::dec_ref(x_47);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_35);
lean::cnstr_set(x_119, 1, x_36);
lean::cnstr_set(x_119, 2, x_37);
lean::cnstr_set(x_119, 3, x_113);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set(x_120, 1, x_110);
lean::cnstr_set(x_120, 2, x_111);
lean::cnstr_set(x_120, 3, x_112);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_120);
lean::cnstr_set(x_1, 2, x_115);
lean::cnstr_set(x_1, 1, x_114);
lean::cnstr_set(x_1, 0, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_46, 3);
lean::inc(x_121);
if (lean::obj_tag(x_121) == 0)
{
uint8 x_122; 
x_122 = !lean::is_exclusive(x_46);
if (x_122 == 0)
{
obj* x_123; obj* x_124; uint8 x_125; 
x_123 = lean::cnstr_get(x_46, 3);
lean::dec(x_123);
x_124 = lean::cnstr_get(x_46, 0);
lean::dec(x_124);
x_125 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_125);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_126; obj* x_127; uint8 x_128; obj* x_129; 
x_126 = lean::cnstr_get(x_46, 1);
x_127 = lean::cnstr_get(x_46, 2);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_46);
x_128 = 0;
x_129 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_129, 0, x_47);
lean::cnstr_set(x_129, 1, x_126);
lean::cnstr_set(x_129, 2, x_127);
lean::cnstr_set(x_129, 3, x_121);
lean::cnstr_set_scalar(x_129, sizeof(void*)*4, x_128);
lean::cnstr_set(x_1, 3, x_129);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8 x_130; 
x_130 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8 x_131; 
lean::free_heap_obj(x_1);
x_131 = !lean::is_exclusive(x_46);
if (x_131 == 0)
{
obj* x_132; obj* x_133; uint8 x_134; 
x_132 = lean::cnstr_get(x_46, 3);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_46, 0);
lean::dec(x_133);
x_134 = !lean::is_exclusive(x_121);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; uint8 x_139; 
x_135 = lean::cnstr_get(x_121, 0);
x_136 = lean::cnstr_get(x_121, 1);
x_137 = lean::cnstr_get(x_121, 2);
x_138 = lean::cnstr_get(x_121, 3);
lean::inc(x_47);
lean::cnstr_set(x_121, 3, x_47);
lean::cnstr_set(x_121, 2, x_37);
lean::cnstr_set(x_121, 1, x_36);
lean::cnstr_set(x_121, 0, x_35);
x_139 = !lean::is_exclusive(x_47);
if (x_139 == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_140 = lean::cnstr_get(x_47, 3);
lean::dec(x_140);
x_141 = lean::cnstr_get(x_47, 2);
lean::dec(x_141);
x_142 = lean::cnstr_get(x_47, 1);
lean::dec(x_142);
x_143 = lean::cnstr_get(x_47, 0);
lean::dec(x_143);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
lean::cnstr_set(x_47, 3, x_138);
lean::cnstr_set(x_47, 2, x_137);
lean::cnstr_set(x_47, 1, x_136);
lean::cnstr_set(x_47, 0, x_135);
lean::cnstr_set(x_46, 3, x_47);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
obj* x_144; 
lean::dec(x_47);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
x_144 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_144, 0, x_135);
lean::cnstr_set(x_144, 1, x_136);
lean::cnstr_set(x_144, 2, x_137);
lean::cnstr_set(x_144, 3, x_138);
lean::cnstr_set_scalar(x_144, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_144);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_121, 0);
x_146 = lean::cnstr_get(x_121, 1);
x_147 = lean::cnstr_get(x_121, 2);
x_148 = lean::cnstr_get(x_121, 3);
lean::inc(x_148);
lean::inc(x_147);
lean::inc(x_146);
lean::inc(x_145);
lean::dec(x_121);
lean::inc(x_47);
x_149 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_149, 0, x_35);
lean::cnstr_set(x_149, 1, x_36);
lean::cnstr_set(x_149, 2, x_37);
lean::cnstr_set(x_149, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_150 = x_47;
} else {
 lean::dec_ref(x_47);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_145);
lean::cnstr_set(x_151, 1, x_146);
lean::cnstr_set(x_151, 2, x_147);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_151);
lean::cnstr_set(x_46, 0, x_149);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_152 = lean::cnstr_get(x_46, 1);
x_153 = lean::cnstr_get(x_46, 2);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_46);
x_154 = lean::cnstr_get(x_121, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_121, 1);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_121, 2);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_121, 3);
lean::inc(x_157);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 lean::cnstr_release(x_121, 2);
 lean::cnstr_release(x_121, 3);
 x_158 = x_121;
} else {
 lean::dec_ref(x_121);
 x_158 = lean::box(0);
}
lean::inc(x_47);
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_35);
lean::cnstr_set(x_159, 1, x_36);
lean::cnstr_set(x_159, 2, x_37);
lean::cnstr_set(x_159, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_160 = x_47;
} else {
 lean::dec_ref(x_47);
 x_160 = lean::box(0);
}
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_154);
lean::cnstr_set(x_161, 1, x_155);
lean::cnstr_set(x_161, 2, x_156);
lean::cnstr_set(x_161, 3, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*4, x_95);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_152);
lean::cnstr_set(x_162, 2, x_153);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8 x_163; 
x_163 = !lean::is_exclusive(x_46);
if (x_163 == 0)
{
obj* x_164; obj* x_165; uint8 x_166; 
x_164 = lean::cnstr_get(x_46, 3);
lean::dec(x_164);
x_165 = lean::cnstr_get(x_46, 0);
lean::dec(x_165);
x_166 = !lean::is_exclusive(x_47);
if (x_166 == 0)
{
uint8 x_167; 
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_167);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; uint8 x_173; 
x_168 = lean::cnstr_get(x_47, 0);
x_169 = lean::cnstr_get(x_47, 1);
x_170 = lean::cnstr_get(x_47, 2);
x_171 = lean::cnstr_get(x_47, 3);
lean::inc(x_171);
lean::inc(x_170);
lean::inc(x_169);
lean::inc(x_168);
lean::dec(x_47);
x_172 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set(x_172, 1, x_169);
lean::cnstr_set(x_172, 2, x_170);
lean::cnstr_set(x_172, 3, x_171);
lean::cnstr_set_scalar(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean::cnstr_set(x_46, 0, x_172);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_173);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; 
x_174 = lean::cnstr_get(x_46, 1);
x_175 = lean::cnstr_get(x_46, 2);
lean::inc(x_175);
lean::inc(x_174);
lean::dec(x_46);
x_176 = lean::cnstr_get(x_47, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_47, 1);
lean::inc(x_177);
x_178 = lean::cnstr_get(x_47, 2);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_47, 3);
lean::inc(x_179);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_180 = x_47;
} else {
 lean::dec_ref(x_47);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_176);
lean::cnstr_set(x_181, 1, x_177);
lean::cnstr_set(x_181, 2, x_178);
lean::cnstr_set(x_181, 3, x_179);
lean::cnstr_set_scalar(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_183, 0, x_181);
lean::cnstr_set(x_183, 1, x_174);
lean::cnstr_set(x_183, 2, x_175);
lean::cnstr_set(x_183, 3, x_121);
lean::cnstr_set_scalar(x_183, sizeof(void*)*4, x_182);
lean::cnstr_set(x_1, 3, x_183);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
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
uint8 x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
obj* x_185; 
x_185 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_35, x_2, x_3);
lean::cnstr_set(x_1, 0, x_185);
return x_1;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_35, x_2, x_3);
if (lean::obj_tag(x_186) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_38);
lean::dec(x_37);
lean::dec(x_36);
return x_186;
}
else
{
obj* x_187; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; 
x_188 = lean::cnstr_get(x_186, 3);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
uint8 x_189; 
x_189 = !lean::is_exclusive(x_186);
if (x_189 == 0)
{
obj* x_190; obj* x_191; uint8 x_192; uint8 x_193; 
x_190 = lean::cnstr_get(x_186, 3);
lean::dec(x_190);
x_191 = lean::cnstr_get(x_186, 0);
lean::dec(x_191);
x_192 = 0;
lean::cnstr_set(x_186, 0, x_188);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
obj* x_194; obj* x_195; uint8 x_196; obj* x_197; uint8 x_198; 
x_194 = lean::cnstr_get(x_186, 1);
x_195 = lean::cnstr_get(x_186, 2);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_186);
x_196 = 0;
x_197 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_197, 0, x_188);
lean::cnstr_set(x_197, 1, x_194);
lean::cnstr_set(x_197, 2, x_195);
lean::cnstr_set(x_197, 3, x_188);
lean::cnstr_set_scalar(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean::cnstr_set(x_1, 0, x_197);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8 x_199; 
x_199 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8 x_200; 
x_200 = !lean::is_exclusive(x_186);
if (x_200 == 0)
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; 
x_201 = lean::cnstr_get(x_186, 1);
x_202 = lean::cnstr_get(x_186, 2);
x_203 = lean::cnstr_get(x_186, 3);
lean::dec(x_203);
x_204 = lean::cnstr_get(x_186, 0);
lean::dec(x_204);
x_205 = !lean::is_exclusive(x_188);
if (x_205 == 0)
{
obj* x_206; obj* x_207; obj* x_208; obj* x_209; uint8 x_210; 
x_206 = lean::cnstr_get(x_188, 0);
x_207 = lean::cnstr_get(x_188, 1);
x_208 = lean::cnstr_get(x_188, 2);
x_209 = lean::cnstr_get(x_188, 3);
x_210 = 1;
lean::cnstr_set(x_188, 3, x_206);
lean::cnstr_set(x_188, 2, x_202);
lean::cnstr_set(x_188, 1, x_201);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set_scalar(x_188, sizeof(void*)*4, x_210);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_209);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_210);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_208);
lean::cnstr_set(x_1, 1, x_207);
lean::cnstr_set(x_1, 0, x_188);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; uint8 x_215; obj* x_216; 
x_211 = lean::cnstr_get(x_188, 0);
x_212 = lean::cnstr_get(x_188, 1);
x_213 = lean::cnstr_get(x_188, 2);
x_214 = lean::cnstr_get(x_188, 3);
lean::inc(x_214);
lean::inc(x_213);
lean::inc(x_212);
lean::inc(x_211);
lean::dec(x_188);
x_215 = 1;
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_187);
lean::cnstr_set(x_216, 1, x_201);
lean::cnstr_set(x_216, 2, x_202);
lean::cnstr_set(x_216, 3, x_211);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_215);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_214);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_215);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_213);
lean::cnstr_set(x_1, 1, x_212);
lean::cnstr_set(x_1, 0, x_216);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; uint8 x_224; obj* x_225; obj* x_226; 
x_217 = lean::cnstr_get(x_186, 1);
x_218 = lean::cnstr_get(x_186, 2);
lean::inc(x_218);
lean::inc(x_217);
lean::dec(x_186);
x_219 = lean::cnstr_get(x_188, 0);
lean::inc(x_219);
x_220 = lean::cnstr_get(x_188, 1);
lean::inc(x_220);
x_221 = lean::cnstr_get(x_188, 2);
lean::inc(x_221);
x_222 = lean::cnstr_get(x_188, 3);
lean::inc(x_222);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 lean::cnstr_release(x_188, 2);
 lean::cnstr_release(x_188, 3);
 x_223 = x_188;
} else {
 lean::dec_ref(x_188);
 x_223 = lean::box(0);
}
x_224 = 1;
if (lean::is_scalar(x_223)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_223;
}
lean::cnstr_set(x_225, 0, x_187);
lean::cnstr_set(x_225, 1, x_217);
lean::cnstr_set(x_225, 2, x_218);
lean::cnstr_set(x_225, 3, x_219);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_224);
x_226 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set(x_226, 1, x_36);
lean::cnstr_set(x_226, 2, x_37);
lean::cnstr_set(x_226, 3, x_38);
lean::cnstr_set_scalar(x_226, sizeof(void*)*4, x_224);
lean::cnstr_set(x_1, 3, x_226);
lean::cnstr_set(x_1, 2, x_221);
lean::cnstr_set(x_1, 1, x_220);
lean::cnstr_set(x_1, 0, x_225);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8 x_227; 
x_227 = !lean::is_exclusive(x_186);
if (x_227 == 0)
{
obj* x_228; obj* x_229; uint8 x_230; 
x_228 = lean::cnstr_get(x_186, 3);
lean::dec(x_228);
x_229 = lean::cnstr_get(x_186, 0);
lean::dec(x_229);
x_230 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_230);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_231; obj* x_232; uint8 x_233; obj* x_234; 
x_231 = lean::cnstr_get(x_186, 1);
x_232 = lean::cnstr_get(x_186, 2);
lean::inc(x_232);
lean::inc(x_231);
lean::dec(x_186);
x_233 = 0;
x_234 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_234, 0, x_187);
lean::cnstr_set(x_234, 1, x_231);
lean::cnstr_set(x_234, 2, x_232);
lean::cnstr_set(x_234, 3, x_188);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 0, x_234);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8 x_235; 
x_235 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8 x_236; 
x_236 = !lean::is_exclusive(x_186);
if (x_236 == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; uint8 x_241; 
x_237 = lean::cnstr_get(x_186, 1);
x_238 = lean::cnstr_get(x_186, 2);
x_239 = lean::cnstr_get(x_186, 3);
x_240 = lean::cnstr_get(x_186, 0);
lean::dec(x_240);
x_241 = !lean::is_exclusive(x_187);
if (x_241 == 0)
{
uint8 x_242; 
x_242 = 1;
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_242);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_242);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; 
x_243 = lean::cnstr_get(x_187, 0);
x_244 = lean::cnstr_get(x_187, 1);
x_245 = lean::cnstr_get(x_187, 2);
x_246 = lean::cnstr_get(x_187, 3);
lean::inc(x_246);
lean::inc(x_245);
lean::inc(x_244);
lean::inc(x_243);
lean::dec(x_187);
x_247 = 1;
x_248 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_248, 0, x_243);
lean::cnstr_set(x_248, 1, x_244);
lean::cnstr_set(x_248, 2, x_245);
lean::cnstr_set(x_248, 3, x_246);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; uint8 x_257; obj* x_258; obj* x_259; 
x_249 = lean::cnstr_get(x_186, 1);
x_250 = lean::cnstr_get(x_186, 2);
x_251 = lean::cnstr_get(x_186, 3);
lean::inc(x_251);
lean::inc(x_250);
lean::inc(x_249);
lean::dec(x_186);
x_252 = lean::cnstr_get(x_187, 0);
lean::inc(x_252);
x_253 = lean::cnstr_get(x_187, 1);
lean::inc(x_253);
x_254 = lean::cnstr_get(x_187, 2);
lean::inc(x_254);
x_255 = lean::cnstr_get(x_187, 3);
lean::inc(x_255);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_256 = x_187;
} else {
 lean::dec_ref(x_187);
 x_256 = lean::box(0);
}
x_257 = 1;
if (lean::is_scalar(x_256)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_256;
}
lean::cnstr_set(x_258, 0, x_252);
lean::cnstr_set(x_258, 1, x_253);
lean::cnstr_set(x_258, 2, x_254);
lean::cnstr_set(x_258, 3, x_255);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
x_259 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_259, 0, x_251);
lean::cnstr_set(x_259, 1, x_36);
lean::cnstr_set(x_259, 2, x_37);
lean::cnstr_set(x_259, 3, x_38);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 3, x_259);
lean::cnstr_set(x_1, 2, x_250);
lean::cnstr_set(x_1, 1, x_249);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_186, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
uint8 x_261; 
x_261 = !lean::is_exclusive(x_186);
if (x_261 == 0)
{
obj* x_262; obj* x_263; uint8 x_264; 
x_262 = lean::cnstr_get(x_186, 3);
lean::dec(x_262);
x_263 = lean::cnstr_get(x_186, 0);
lean::dec(x_263);
x_264 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_264);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_265; obj* x_266; uint8 x_267; obj* x_268; 
x_265 = lean::cnstr_get(x_186, 1);
x_266 = lean::cnstr_get(x_186, 2);
lean::inc(x_266);
lean::inc(x_265);
lean::dec(x_186);
x_267 = 0;
x_268 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_268, 0, x_187);
lean::cnstr_set(x_268, 1, x_265);
lean::cnstr_set(x_268, 2, x_266);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
lean::cnstr_set(x_1, 0, x_268);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8 x_269; 
x_269 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8 x_270; 
lean::free_heap_obj(x_1);
x_270 = !lean::is_exclusive(x_186);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; uint8 x_275; 
x_271 = lean::cnstr_get(x_186, 1);
x_272 = lean::cnstr_get(x_186, 2);
x_273 = lean::cnstr_get(x_186, 3);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_186, 0);
lean::dec(x_274);
x_275 = !lean::is_exclusive(x_260);
if (x_275 == 0)
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; uint8 x_280; 
x_276 = lean::cnstr_get(x_260, 0);
x_277 = lean::cnstr_get(x_260, 1);
x_278 = lean::cnstr_get(x_260, 2);
x_279 = lean::cnstr_get(x_260, 3);
lean::inc(x_187);
lean::cnstr_set(x_260, 3, x_276);
lean::cnstr_set(x_260, 2, x_272);
lean::cnstr_set(x_260, 1, x_271);
lean::cnstr_set(x_260, 0, x_187);
x_280 = !lean::is_exclusive(x_187);
if (x_280 == 0)
{
obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_281 = lean::cnstr_get(x_187, 3);
lean::dec(x_281);
x_282 = lean::cnstr_get(x_187, 2);
lean::dec(x_282);
x_283 = lean::cnstr_get(x_187, 1);
lean::dec(x_283);
x_284 = lean::cnstr_get(x_187, 0);
lean::dec(x_284);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
lean::cnstr_set(x_187, 3, x_38);
lean::cnstr_set(x_187, 2, x_37);
lean::cnstr_set(x_187, 1, x_36);
lean::cnstr_set(x_187, 0, x_279);
lean::cnstr_set(x_186, 3, x_187);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
obj* x_285; 
lean::dec(x_187);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
x_285 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_285, 0, x_279);
lean::cnstr_set(x_285, 1, x_36);
lean::cnstr_set(x_285, 2, x_37);
lean::cnstr_set(x_285, 3, x_38);
lean::cnstr_set_scalar(x_285, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_285);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
x_286 = lean::cnstr_get(x_260, 0);
x_287 = lean::cnstr_get(x_260, 1);
x_288 = lean::cnstr_get(x_260, 2);
x_289 = lean::cnstr_get(x_260, 3);
lean::inc(x_289);
lean::inc(x_288);
lean::inc(x_287);
lean::inc(x_286);
lean::dec(x_260);
lean::inc(x_187);
x_290 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_290, 0, x_187);
lean::cnstr_set(x_290, 1, x_271);
lean::cnstr_set(x_290, 2, x_272);
lean::cnstr_set(x_290, 3, x_286);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_291 = x_187;
} else {
 lean::dec_ref(x_187);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_289);
lean::cnstr_set(x_292, 1, x_36);
lean::cnstr_set(x_292, 2, x_37);
lean::cnstr_set(x_292, 3, x_38);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_292);
lean::cnstr_set(x_186, 2, x_288);
lean::cnstr_set(x_186, 1, x_287);
lean::cnstr_set(x_186, 0, x_290);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_293 = lean::cnstr_get(x_186, 1);
x_294 = lean::cnstr_get(x_186, 2);
lean::inc(x_294);
lean::inc(x_293);
lean::dec(x_186);
x_295 = lean::cnstr_get(x_260, 0);
lean::inc(x_295);
x_296 = lean::cnstr_get(x_260, 1);
lean::inc(x_296);
x_297 = lean::cnstr_get(x_260, 2);
lean::inc(x_297);
x_298 = lean::cnstr_get(x_260, 3);
lean::inc(x_298);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 lean::cnstr_release(x_260, 2);
 lean::cnstr_release(x_260, 3);
 x_299 = x_260;
} else {
 lean::dec_ref(x_260);
 x_299 = lean::box(0);
}
lean::inc(x_187);
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_187);
lean::cnstr_set(x_300, 1, x_293);
lean::cnstr_set(x_300, 2, x_294);
lean::cnstr_set(x_300, 3, x_295);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_301 = x_187;
} else {
 lean::dec_ref(x_187);
 x_301 = lean::box(0);
}
lean::cnstr_set_scalar(x_300, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_301)) {
 x_302 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_302 = x_301;
}
lean::cnstr_set(x_302, 0, x_298);
lean::cnstr_set(x_302, 1, x_36);
lean::cnstr_set(x_302, 2, x_37);
lean::cnstr_set(x_302, 3, x_38);
lean::cnstr_set_scalar(x_302, sizeof(void*)*4, x_235);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_296);
lean::cnstr_set(x_303, 2, x_297);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8 x_304; 
x_304 = !lean::is_exclusive(x_186);
if (x_304 == 0)
{
obj* x_305; obj* x_306; uint8 x_307; 
x_305 = lean::cnstr_get(x_186, 3);
lean::dec(x_305);
x_306 = lean::cnstr_get(x_186, 0);
lean::dec(x_306);
x_307 = !lean::is_exclusive(x_187);
if (x_307 == 0)
{
uint8 x_308; 
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_308);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; uint8 x_314; 
x_309 = lean::cnstr_get(x_187, 0);
x_310 = lean::cnstr_get(x_187, 1);
x_311 = lean::cnstr_get(x_187, 2);
x_312 = lean::cnstr_get(x_187, 3);
lean::inc(x_312);
lean::inc(x_311);
lean::inc(x_310);
lean::inc(x_309);
lean::dec(x_187);
x_313 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_313, 0, x_309);
lean::cnstr_set(x_313, 1, x_310);
lean::cnstr_set(x_313, 2, x_311);
lean::cnstr_set(x_313, 3, x_312);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean::cnstr_set(x_186, 0, x_313);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_314);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; uint8 x_323; obj* x_324; 
x_315 = lean::cnstr_get(x_186, 1);
x_316 = lean::cnstr_get(x_186, 2);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_186);
x_317 = lean::cnstr_get(x_187, 0);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_187, 1);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_187, 2);
lean::inc(x_319);
x_320 = lean::cnstr_get(x_187, 3);
lean::inc(x_320);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_321 = x_187;
} else {
 lean::dec_ref(x_187);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_317);
lean::cnstr_set(x_322, 1, x_318);
lean::cnstr_set(x_322, 2, x_319);
lean::cnstr_set(x_322, 3, x_320);
lean::cnstr_set_scalar(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_322);
lean::cnstr_set(x_324, 1, x_315);
lean::cnstr_set(x_324, 2, x_316);
lean::cnstr_set(x_324, 3, x_260);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_323);
lean::cnstr_set(x_1, 0, x_324);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
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
obj* x_325; obj* x_326; obj* x_327; obj* x_328; uint32 x_329; uint8 x_330; 
x_325 = lean::cnstr_get(x_1, 0);
x_326 = lean::cnstr_get(x_1, 1);
x_327 = lean::cnstr_get(x_1, 2);
x_328 = lean::cnstr_get(x_1, 3);
lean::inc(x_328);
lean::inc(x_327);
lean::inc(x_326);
lean::inc(x_325);
lean::dec(x_1);
x_329 = lean::unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32 x_331; uint8 x_332; 
x_331 = lean::unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
obj* x_333; obj* x_334; 
lean::dec(x_327);
lean::dec(x_326);
x_333 = lean::box_uint32(x_2);
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_325);
lean::cnstr_set(x_334, 1, x_333);
lean::cnstr_set(x_334, 2, x_3);
lean::cnstr_set(x_334, 3, x_328);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8 x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
obj* x_336; obj* x_337; 
x_336 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_328, x_2, x_3);
x_337 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_337, 0, x_325);
lean::cnstr_set(x_337, 1, x_326);
lean::cnstr_set(x_337, 2, x_327);
lean::cnstr_set(x_337, 3, x_336);
lean::cnstr_set_scalar(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
obj* x_338; 
x_338 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_328, x_2, x_3);
if (lean::obj_tag(x_338) == 0)
{
lean::dec(x_327);
lean::dec(x_326);
lean::dec(x_325);
return x_338;
}
else
{
obj* x_339; 
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
if (lean::obj_tag(x_339) == 0)
{
obj* x_340; 
x_340 = lean::cnstr_get(x_338, 3);
lean::inc(x_340);
if (lean::obj_tag(x_340) == 0)
{
obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; uint8 x_346; obj* x_347; 
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_338, 2);
lean::inc(x_342);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_343 = x_338;
} else {
 lean::dec_ref(x_338);
 x_343 = lean::box(0);
}
x_344 = 0;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_340);
lean::cnstr_set(x_345, 1, x_341);
lean::cnstr_set(x_345, 2, x_342);
lean::cnstr_set(x_345, 3, x_340);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_325);
lean::cnstr_set(x_347, 1, x_326);
lean::cnstr_set(x_347, 2, x_327);
lean::cnstr_set(x_347, 3, x_345);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8 x_348; 
x_348 = lean::cnstr_get_scalar<uint8>(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; uint8 x_357; obj* x_358; obj* x_359; obj* x_360; 
x_349 = lean::cnstr_get(x_338, 1);
lean::inc(x_349);
x_350 = lean::cnstr_get(x_338, 2);
lean::inc(x_350);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_351 = x_338;
} else {
 lean::dec_ref(x_338);
 x_351 = lean::box(0);
}
x_352 = lean::cnstr_get(x_340, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_340, 1);
lean::inc(x_353);
x_354 = lean::cnstr_get(x_340, 2);
lean::inc(x_354);
x_355 = lean::cnstr_get(x_340, 3);
lean::inc(x_355);
if (lean::is_exclusive(x_340)) {
 lean::cnstr_release(x_340, 0);
 lean::cnstr_release(x_340, 1);
 lean::cnstr_release(x_340, 2);
 lean::cnstr_release(x_340, 3);
 x_356 = x_340;
} else {
 lean::dec_ref(x_340);
 x_356 = lean::box(0);
}
x_357 = 1;
if (lean::is_scalar(x_356)) {
 x_358 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_358 = x_356;
}
lean::cnstr_set(x_358, 0, x_325);
lean::cnstr_set(x_358, 1, x_326);
lean::cnstr_set(x_358, 2, x_327);
lean::cnstr_set(x_358, 3, x_339);
lean::cnstr_set_scalar(x_358, sizeof(void*)*4, x_357);
if (lean::is_scalar(x_351)) {
 x_359 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_359 = x_351;
}
lean::cnstr_set(x_359, 0, x_352);
lean::cnstr_set(x_359, 1, x_353);
lean::cnstr_set(x_359, 2, x_354);
lean::cnstr_set(x_359, 3, x_355);
lean::cnstr_set_scalar(x_359, sizeof(void*)*4, x_357);
x_360 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_360, 0, x_358);
lean::cnstr_set(x_360, 1, x_349);
lean::cnstr_set(x_360, 2, x_350);
lean::cnstr_set(x_360, 3, x_359);
lean::cnstr_set_scalar(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; 
x_361 = lean::cnstr_get(x_338, 1);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_338, 2);
lean::inc(x_362);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_363 = x_338;
} else {
 lean::dec_ref(x_338);
 x_363 = lean::box(0);
}
x_364 = 0;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_339);
lean::cnstr_set(x_365, 1, x_361);
lean::cnstr_set(x_365, 2, x_362);
lean::cnstr_set(x_365, 3, x_340);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
x_366 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_366, 0, x_325);
lean::cnstr_set(x_366, 1, x_326);
lean::cnstr_set(x_366, 2, x_327);
lean::cnstr_set(x_366, 3, x_365);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8 x_367; 
x_367 = lean::cnstr_get_scalar<uint8>(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; uint8 x_377; obj* x_378; obj* x_379; obj* x_380; 
x_368 = lean::cnstr_get(x_338, 1);
lean::inc(x_368);
x_369 = lean::cnstr_get(x_338, 2);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_338, 3);
lean::inc(x_370);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_371 = x_338;
} else {
 lean::dec_ref(x_338);
 x_371 = lean::box(0);
}
x_372 = lean::cnstr_get(x_339, 0);
lean::inc(x_372);
x_373 = lean::cnstr_get(x_339, 1);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_339, 2);
lean::inc(x_374);
x_375 = lean::cnstr_get(x_339, 3);
lean::inc(x_375);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_376 = x_339;
} else {
 lean::dec_ref(x_339);
 x_376 = lean::box(0);
}
x_377 = 1;
if (lean::is_scalar(x_376)) {
 x_378 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_378 = x_376;
}
lean::cnstr_set(x_378, 0, x_325);
lean::cnstr_set(x_378, 1, x_326);
lean::cnstr_set(x_378, 2, x_327);
lean::cnstr_set(x_378, 3, x_372);
lean::cnstr_set_scalar(x_378, sizeof(void*)*4, x_377);
if (lean::is_scalar(x_371)) {
 x_379 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_379 = x_371;
}
lean::cnstr_set(x_379, 0, x_375);
lean::cnstr_set(x_379, 1, x_368);
lean::cnstr_set(x_379, 2, x_369);
lean::cnstr_set(x_379, 3, x_370);
lean::cnstr_set_scalar(x_379, sizeof(void*)*4, x_377);
x_380 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_380, 0, x_378);
lean::cnstr_set(x_380, 1, x_373);
lean::cnstr_set(x_380, 2, x_374);
lean::cnstr_set(x_380, 3, x_379);
lean::cnstr_set_scalar(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
obj* x_381; 
x_381 = lean::cnstr_get(x_338, 3);
lean::inc(x_381);
if (lean::obj_tag(x_381) == 0)
{
obj* x_382; obj* x_383; obj* x_384; uint8 x_385; obj* x_386; obj* x_387; 
x_382 = lean::cnstr_get(x_338, 1);
lean::inc(x_382);
x_383 = lean::cnstr_get(x_338, 2);
lean::inc(x_383);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_384 = x_338;
} else {
 lean::dec_ref(x_338);
 x_384 = lean::box(0);
}
x_385 = 0;
if (lean::is_scalar(x_384)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_384;
}
lean::cnstr_set(x_386, 0, x_339);
lean::cnstr_set(x_386, 1, x_382);
lean::cnstr_set(x_386, 2, x_383);
lean::cnstr_set(x_386, 3, x_381);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_385);
x_387 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_387, 0, x_325);
lean::cnstr_set(x_387, 1, x_326);
lean::cnstr_set(x_387, 2, x_327);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8 x_388; 
x_388 = lean::cnstr_get_scalar<uint8>(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; 
x_389 = lean::cnstr_get(x_338, 1);
lean::inc(x_389);
x_390 = lean::cnstr_get(x_338, 2);
lean::inc(x_390);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_391 = x_338;
} else {
 lean::dec_ref(x_338);
 x_391 = lean::box(0);
}
x_392 = lean::cnstr_get(x_381, 0);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_381, 1);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_381, 2);
lean::inc(x_394);
x_395 = lean::cnstr_get(x_381, 3);
lean::inc(x_395);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 lean::cnstr_release(x_381, 1);
 lean::cnstr_release(x_381, 2);
 lean::cnstr_release(x_381, 3);
 x_396 = x_381;
} else {
 lean::dec_ref(x_381);
 x_396 = lean::box(0);
}
lean::inc(x_339);
if (lean::is_scalar(x_396)) {
 x_397 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_397 = x_396;
}
lean::cnstr_set(x_397, 0, x_325);
lean::cnstr_set(x_397, 1, x_326);
lean::cnstr_set(x_397, 2, x_327);
lean::cnstr_set(x_397, 3, x_339);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_398 = x_339;
} else {
 lean::dec_ref(x_339);
 x_398 = lean::box(0);
}
lean::cnstr_set_scalar(x_397, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_392);
lean::cnstr_set(x_399, 1, x_393);
lean::cnstr_set(x_399, 2, x_394);
lean::cnstr_set(x_399, 3, x_395);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_391)) {
 x_400 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_400 = x_391;
}
lean::cnstr_set(x_400, 0, x_397);
lean::cnstr_set(x_400, 1, x_389);
lean::cnstr_set(x_400, 2, x_390);
lean::cnstr_set(x_400, 3, x_399);
lean::cnstr_set_scalar(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; uint8 x_410; obj* x_411; obj* x_412; 
x_401 = lean::cnstr_get(x_338, 1);
lean::inc(x_401);
x_402 = lean::cnstr_get(x_338, 2);
lean::inc(x_402);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_403 = x_338;
} else {
 lean::dec_ref(x_338);
 x_403 = lean::box(0);
}
x_404 = lean::cnstr_get(x_339, 0);
lean::inc(x_404);
x_405 = lean::cnstr_get(x_339, 1);
lean::inc(x_405);
x_406 = lean::cnstr_get(x_339, 2);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_339, 3);
lean::inc(x_407);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_408 = x_339;
} else {
 lean::dec_ref(x_339);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_404);
lean::cnstr_set(x_409, 1, x_405);
lean::cnstr_set(x_409, 2, x_406);
lean::cnstr_set(x_409, 3, x_407);
lean::cnstr_set_scalar(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean::is_scalar(x_403)) {
 x_411 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_411 = x_403;
}
lean::cnstr_set(x_411, 0, x_409);
lean::cnstr_set(x_411, 1, x_401);
lean::cnstr_set(x_411, 2, x_402);
lean::cnstr_set(x_411, 3, x_381);
lean::cnstr_set_scalar(x_411, sizeof(void*)*4, x_410);
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_325);
lean::cnstr_set(x_412, 1, x_326);
lean::cnstr_set(x_412, 2, x_327);
lean::cnstr_set(x_412, 3, x_411);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_388);
return x_412;
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
uint8 x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
obj* x_414; obj* x_415; 
x_414 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_325, x_2, x_3);
x_415 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_415, 0, x_414);
lean::cnstr_set(x_415, 1, x_326);
lean::cnstr_set(x_415, 2, x_327);
lean::cnstr_set(x_415, 3, x_328);
lean::cnstr_set_scalar(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
obj* x_416; 
x_416 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_325, x_2, x_3);
if (lean::obj_tag(x_416) == 0)
{
lean::dec(x_328);
lean::dec(x_327);
lean::dec(x_326);
return x_416;
}
else
{
obj* x_417; 
x_417 = lean::cnstr_get(x_416, 0);
lean::inc(x_417);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; 
x_418 = lean::cnstr_get(x_416, 3);
lean::inc(x_418);
if (lean::obj_tag(x_418) == 0)
{
obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; uint8 x_424; obj* x_425; 
x_419 = lean::cnstr_get(x_416, 1);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_416, 2);
lean::inc(x_420);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_421 = x_416;
} else {
 lean::dec_ref(x_416);
 x_421 = lean::box(0);
}
x_422 = 0;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_418);
lean::cnstr_set(x_423, 1, x_419);
lean::cnstr_set(x_423, 2, x_420);
lean::cnstr_set(x_423, 3, x_418);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_326);
lean::cnstr_set(x_425, 2, x_327);
lean::cnstr_set(x_425, 3, x_328);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8 x_426; 
x_426 = lean::cnstr_get_scalar<uint8>(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; uint8 x_435; obj* x_436; obj* x_437; obj* x_438; 
x_427 = lean::cnstr_get(x_416, 1);
lean::inc(x_427);
x_428 = lean::cnstr_get(x_416, 2);
lean::inc(x_428);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_429 = x_416;
} else {
 lean::dec_ref(x_416);
 x_429 = lean::box(0);
}
x_430 = lean::cnstr_get(x_418, 0);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_418, 1);
lean::inc(x_431);
x_432 = lean::cnstr_get(x_418, 2);
lean::inc(x_432);
x_433 = lean::cnstr_get(x_418, 3);
lean::inc(x_433);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 lean::cnstr_release(x_418, 2);
 lean::cnstr_release(x_418, 3);
 x_434 = x_418;
} else {
 lean::dec_ref(x_418);
 x_434 = lean::box(0);
}
x_435 = 1;
if (lean::is_scalar(x_434)) {
 x_436 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_436 = x_434;
}
lean::cnstr_set(x_436, 0, x_417);
lean::cnstr_set(x_436, 1, x_427);
lean::cnstr_set(x_436, 2, x_428);
lean::cnstr_set(x_436, 3, x_430);
lean::cnstr_set_scalar(x_436, sizeof(void*)*4, x_435);
if (lean::is_scalar(x_429)) {
 x_437 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_437 = x_429;
}
lean::cnstr_set(x_437, 0, x_433);
lean::cnstr_set(x_437, 1, x_326);
lean::cnstr_set(x_437, 2, x_327);
lean::cnstr_set(x_437, 3, x_328);
lean::cnstr_set_scalar(x_437, sizeof(void*)*4, x_435);
x_438 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_438, 0, x_436);
lean::cnstr_set(x_438, 1, x_431);
lean::cnstr_set(x_438, 2, x_432);
lean::cnstr_set(x_438, 3, x_437);
lean::cnstr_set_scalar(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; 
x_439 = lean::cnstr_get(x_416, 1);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_416, 2);
lean::inc(x_440);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_441 = x_416;
} else {
 lean::dec_ref(x_416);
 x_441 = lean::box(0);
}
x_442 = 0;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_417);
lean::cnstr_set(x_443, 1, x_439);
lean::cnstr_set(x_443, 2, x_440);
lean::cnstr_set(x_443, 3, x_418);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
x_444 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_444, 0, x_443);
lean::cnstr_set(x_444, 1, x_326);
lean::cnstr_set(x_444, 2, x_327);
lean::cnstr_set(x_444, 3, x_328);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8 x_445; 
x_445 = lean::cnstr_get_scalar<uint8>(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; 
x_446 = lean::cnstr_get(x_416, 1);
lean::inc(x_446);
x_447 = lean::cnstr_get(x_416, 2);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_416, 3);
lean::inc(x_448);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_449 = x_416;
} else {
 lean::dec_ref(x_416);
 x_449 = lean::box(0);
}
x_450 = lean::cnstr_get(x_417, 0);
lean::inc(x_450);
x_451 = lean::cnstr_get(x_417, 1);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_417, 2);
lean::inc(x_452);
x_453 = lean::cnstr_get(x_417, 3);
lean::inc(x_453);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_454 = x_417;
} else {
 lean::dec_ref(x_417);
 x_454 = lean::box(0);
}
x_455 = 1;
if (lean::is_scalar(x_454)) {
 x_456 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_456 = x_454;
}
lean::cnstr_set(x_456, 0, x_450);
lean::cnstr_set(x_456, 1, x_451);
lean::cnstr_set(x_456, 2, x_452);
lean::cnstr_set(x_456, 3, x_453);
lean::cnstr_set_scalar(x_456, sizeof(void*)*4, x_455);
if (lean::is_scalar(x_449)) {
 x_457 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_457 = x_449;
}
lean::cnstr_set(x_457, 0, x_448);
lean::cnstr_set(x_457, 1, x_326);
lean::cnstr_set(x_457, 2, x_327);
lean::cnstr_set(x_457, 3, x_328);
lean::cnstr_set_scalar(x_457, sizeof(void*)*4, x_455);
x_458 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_458, 0, x_456);
lean::cnstr_set(x_458, 1, x_446);
lean::cnstr_set(x_458, 2, x_447);
lean::cnstr_set(x_458, 3, x_457);
lean::cnstr_set_scalar(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
obj* x_459; 
x_459 = lean::cnstr_get(x_416, 3);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_460; obj* x_461; obj* x_462; uint8 x_463; obj* x_464; obj* x_465; 
x_460 = lean::cnstr_get(x_416, 1);
lean::inc(x_460);
x_461 = lean::cnstr_get(x_416, 2);
lean::inc(x_461);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_462 = x_416;
} else {
 lean::dec_ref(x_416);
 x_462 = lean::box(0);
}
x_463 = 0;
if (lean::is_scalar(x_462)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_462;
}
lean::cnstr_set(x_464, 0, x_417);
lean::cnstr_set(x_464, 1, x_460);
lean::cnstr_set(x_464, 2, x_461);
lean::cnstr_set(x_464, 3, x_459);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_463);
x_465 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_326);
lean::cnstr_set(x_465, 2, x_327);
lean::cnstr_set(x_465, 3, x_328);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8 x_466; 
x_466 = lean::cnstr_get_scalar<uint8>(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; 
x_467 = lean::cnstr_get(x_416, 1);
lean::inc(x_467);
x_468 = lean::cnstr_get(x_416, 2);
lean::inc(x_468);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_469 = x_416;
} else {
 lean::dec_ref(x_416);
 x_469 = lean::box(0);
}
x_470 = lean::cnstr_get(x_459, 0);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_459, 1);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_459, 2);
lean::inc(x_472);
x_473 = lean::cnstr_get(x_459, 3);
lean::inc(x_473);
if (lean::is_exclusive(x_459)) {
 lean::cnstr_release(x_459, 0);
 lean::cnstr_release(x_459, 1);
 lean::cnstr_release(x_459, 2);
 lean::cnstr_release(x_459, 3);
 x_474 = x_459;
} else {
 lean::dec_ref(x_459);
 x_474 = lean::box(0);
}
lean::inc(x_417);
if (lean::is_scalar(x_474)) {
 x_475 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_475 = x_474;
}
lean::cnstr_set(x_475, 0, x_417);
lean::cnstr_set(x_475, 1, x_467);
lean::cnstr_set(x_475, 2, x_468);
lean::cnstr_set(x_475, 3, x_470);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_476 = x_417;
} else {
 lean::dec_ref(x_417);
 x_476 = lean::box(0);
}
lean::cnstr_set_scalar(x_475, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_476)) {
 x_477 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_477 = x_476;
}
lean::cnstr_set(x_477, 0, x_473);
lean::cnstr_set(x_477, 1, x_326);
lean::cnstr_set(x_477, 2, x_327);
lean::cnstr_set(x_477, 3, x_328);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_469)) {
 x_478 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_478 = x_469;
}
lean::cnstr_set(x_478, 0, x_475);
lean::cnstr_set(x_478, 1, x_471);
lean::cnstr_set(x_478, 2, x_472);
lean::cnstr_set(x_478, 3, x_477);
lean::cnstr_set_scalar(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; uint8 x_488; obj* x_489; obj* x_490; 
x_479 = lean::cnstr_get(x_416, 1);
lean::inc(x_479);
x_480 = lean::cnstr_get(x_416, 2);
lean::inc(x_480);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_481 = x_416;
} else {
 lean::dec_ref(x_416);
 x_481 = lean::box(0);
}
x_482 = lean::cnstr_get(x_417, 0);
lean::inc(x_482);
x_483 = lean::cnstr_get(x_417, 1);
lean::inc(x_483);
x_484 = lean::cnstr_get(x_417, 2);
lean::inc(x_484);
x_485 = lean::cnstr_get(x_417, 3);
lean::inc(x_485);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_486 = x_417;
} else {
 lean::dec_ref(x_417);
 x_486 = lean::box(0);
}
if (lean::is_scalar(x_486)) {
 x_487 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_487 = x_486;
}
lean::cnstr_set(x_487, 0, x_482);
lean::cnstr_set(x_487, 1, x_483);
lean::cnstr_set(x_487, 2, x_484);
lean::cnstr_set(x_487, 3, x_485);
lean::cnstr_set_scalar(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean::is_scalar(x_481)) {
 x_489 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_489 = x_481;
}
lean::cnstr_set(x_489, 0, x_487);
lean::cnstr_set(x_489, 1, x_479);
lean::cnstr_set(x_489, 2, x_480);
lean::cnstr_set(x_489, 3, x_459);
lean::cnstr_set_scalar(x_489, sizeof(void*)*4, x_488);
x_490 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_490, 0, x_489);
lean::cnstr_set(x_490, 1, x_326);
lean::cnstr_set(x_490, 2, x_327);
lean::cnstr_set(x_490, 3, x_328);
lean::cnstr_set_scalar(x_490, sizeof(void*)*4, x_466);
return x_490;
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
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::box_uint32(x_2);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
x_13 = lean::unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = lean::unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_11);
lean::dec(x_10);
x_17 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_17);
return x_1;
}
else
{
obj* x_18; 
x_18 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_12, x_2, x_3);
lean::cnstr_set(x_1, 3, x_18);
return x_1;
}
}
else
{
obj* x_19; 
x_19 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_9, x_2, x_3);
lean::cnstr_set(x_1, 0, x_19);
return x_1;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint32 x_24; uint8 x_25; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = lean::cnstr_get(x_1, 2);
x_23 = lean::cnstr_get(x_1, 3);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_1);
x_24 = lean::unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = lean::unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
lean::dec(x_21);
x_28 = lean::box_uint32(x_2);
x_29 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_29, 0, x_20);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set(x_29, 2, x_3);
lean::cnstr_set(x_29, 3, x_23);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
obj* x_30; obj* x_31; 
x_30 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_23, x_2, x_3);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_20);
lean::cnstr_set(x_31, 1, x_21);
lean::cnstr_set(x_31, 2, x_22);
lean::cnstr_set(x_31, 3, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; 
x_32 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_20, x_2, x_3);
x_33 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_21);
lean::cnstr_set(x_33, 2, x_22);
lean::cnstr_set(x_33, 3, x_23);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8 x_34; 
x_34 = !lean::is_exclusive(x_1);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint32 x_39; uint8 x_40; 
x_35 = lean::cnstr_get(x_1, 0);
x_36 = lean::cnstr_get(x_1, 1);
x_37 = lean::cnstr_get(x_1, 2);
x_38 = lean::cnstr_get(x_1, 3);
x_39 = lean::unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = lean::unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
obj* x_43; 
lean::dec(x_37);
lean::dec(x_36);
x_43 = lean::box_uint32(x_2);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8 x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
obj* x_45; 
x_45 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_38, x_2, x_3);
lean::cnstr_set(x_1, 3, x_45);
return x_1;
}
else
{
obj* x_46; 
x_46 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_38, x_2, x_3);
if (lean::obj_tag(x_46) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_35);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; 
x_48 = lean::cnstr_get(x_46, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
uint8 x_49; 
x_49 = !lean::is_exclusive(x_46);
if (x_49 == 0)
{
obj* x_50; obj* x_51; uint8 x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_46, 3);
lean::dec(x_50);
x_51 = lean::cnstr_get(x_46, 0);
lean::dec(x_51);
x_52 = 0;
lean::cnstr_set(x_46, 0, x_48);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
obj* x_54; obj* x_55; uint8 x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_46, 1);
x_55 = lean::cnstr_get(x_46, 2);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_46);
x_56 = 0;
x_57 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_57, 0, x_48);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_55);
lean::cnstr_set(x_57, 3, x_48);
lean::cnstr_set_scalar(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean::cnstr_set(x_1, 3, x_57);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8 x_59; 
x_59 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8 x_60; 
x_60 = !lean::is_exclusive(x_46);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_61 = lean::cnstr_get(x_46, 1);
x_62 = lean::cnstr_get(x_46, 2);
x_63 = lean::cnstr_get(x_46, 3);
lean::dec(x_63);
x_64 = lean::cnstr_get(x_46, 0);
lean::dec(x_64);
x_65 = !lean::is_exclusive(x_48);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; uint8 x_70; 
x_66 = lean::cnstr_get(x_48, 0);
x_67 = lean::cnstr_get(x_48, 1);
x_68 = lean::cnstr_get(x_48, 2);
x_69 = lean::cnstr_get(x_48, 3);
x_70 = 1;
lean::cnstr_set(x_48, 3, x_47);
lean::cnstr_set(x_48, 2, x_37);
lean::cnstr_set(x_48, 1, x_36);
lean::cnstr_set(x_48, 0, x_35);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_70);
lean::cnstr_set(x_46, 3, x_69);
lean::cnstr_set(x_46, 2, x_68);
lean::cnstr_set(x_46, 1, x_67);
lean::cnstr_set(x_46, 0, x_66);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_70);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_48);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; uint8 x_75; obj* x_76; 
x_71 = lean::cnstr_get(x_48, 0);
x_72 = lean::cnstr_get(x_48, 1);
x_73 = lean::cnstr_get(x_48, 2);
x_74 = lean::cnstr_get(x_48, 3);
lean::inc(x_74);
lean::inc(x_73);
lean::inc(x_72);
lean::inc(x_71);
lean::dec(x_48);
x_75 = 1;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_35);
lean::cnstr_set(x_76, 1, x_36);
lean::cnstr_set(x_76, 2, x_37);
lean::cnstr_set(x_76, 3, x_47);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_75);
lean::cnstr_set(x_46, 3, x_74);
lean::cnstr_set(x_46, 2, x_73);
lean::cnstr_set(x_46, 1, x_72);
lean::cnstr_set(x_46, 0, x_71);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_75);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_62);
lean::cnstr_set(x_1, 1, x_61);
lean::cnstr_set(x_1, 0, x_76);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; 
x_77 = lean::cnstr_get(x_46, 1);
x_78 = lean::cnstr_get(x_46, 2);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_46);
x_79 = lean::cnstr_get(x_48, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_48, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_48, 2);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_48, 3);
lean::inc(x_82);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 lean::cnstr_release(x_48, 2);
 lean::cnstr_release(x_48, 3);
 x_83 = x_48;
} else {
 lean::dec_ref(x_48);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_35);
lean::cnstr_set(x_85, 1, x_36);
lean::cnstr_set(x_85, 2, x_37);
lean::cnstr_set(x_85, 3, x_47);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_79);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_81);
lean::cnstr_set(x_86, 3, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_84);
lean::cnstr_set(x_1, 3, x_86);
lean::cnstr_set(x_1, 2, x_78);
lean::cnstr_set(x_1, 1, x_77);
lean::cnstr_set(x_1, 0, x_85);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_46);
if (x_87 == 0)
{
obj* x_88; obj* x_89; uint8 x_90; 
x_88 = lean::cnstr_get(x_46, 3);
lean::dec(x_88);
x_89 = lean::cnstr_get(x_46, 0);
lean::dec(x_89);
x_90 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_90);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
obj* x_91; obj* x_92; uint8 x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_46, 1);
x_92 = lean::cnstr_get(x_46, 2);
lean::inc(x_92);
lean::inc(x_91);
lean::dec(x_46);
x_93 = 0;
x_94 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_94, 0, x_47);
lean::cnstr_set(x_94, 1, x_91);
lean::cnstr_set(x_94, 2, x_92);
lean::cnstr_set(x_94, 3, x_48);
lean::cnstr_set_scalar(x_94, sizeof(void*)*4, x_93);
lean::cnstr_set(x_1, 3, x_94);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8 x_95; 
x_95 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8 x_96; 
x_96 = !lean::is_exclusive(x_46);
if (x_96 == 0)
{
obj* x_97; uint8 x_98; 
x_97 = lean::cnstr_get(x_46, 0);
lean::dec(x_97);
x_98 = !lean::is_exclusive(x_47);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; uint8 x_103; 
x_99 = lean::cnstr_get(x_47, 0);
x_100 = lean::cnstr_get(x_47, 1);
x_101 = lean::cnstr_get(x_47, 2);
x_102 = lean::cnstr_get(x_47, 3);
x_103 = 1;
lean::cnstr_set(x_47, 3, x_99);
lean::cnstr_set(x_47, 2, x_37);
lean::cnstr_set(x_47, 1, x_36);
lean::cnstr_set(x_47, 0, x_35);
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_103);
lean::cnstr_set(x_46, 0, x_102);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_103);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_101);
lean::cnstr_set(x_1, 1, x_100);
lean::cnstr_set(x_1, 0, x_47);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; 
x_104 = lean::cnstr_get(x_47, 0);
x_105 = lean::cnstr_get(x_47, 1);
x_106 = lean::cnstr_get(x_47, 2);
x_107 = lean::cnstr_get(x_47, 3);
lean::inc(x_107);
lean::inc(x_106);
lean::inc(x_105);
lean::inc(x_104);
lean::dec(x_47);
x_108 = 1;
x_109 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_109, 0, x_35);
lean::cnstr_set(x_109, 1, x_36);
lean::cnstr_set(x_109, 2, x_37);
lean::cnstr_set(x_109, 3, x_104);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_108);
lean::cnstr_set(x_46, 0, x_107);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_108);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set(x_1, 2, x_106);
lean::cnstr_set(x_1, 1, x_105);
lean::cnstr_set(x_1, 0, x_109);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; 
x_110 = lean::cnstr_get(x_46, 1);
x_111 = lean::cnstr_get(x_46, 2);
x_112 = lean::cnstr_get(x_46, 3);
lean::inc(x_112);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_46);
x_113 = lean::cnstr_get(x_47, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get(x_47, 1);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_47, 2);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_47, 3);
lean::inc(x_116);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_117 = x_47;
} else {
 lean::dec_ref(x_47);
 x_117 = lean::box(0);
}
x_118 = 1;
if (lean::is_scalar(x_117)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_117;
}
lean::cnstr_set(x_119, 0, x_35);
lean::cnstr_set(x_119, 1, x_36);
lean::cnstr_set(x_119, 2, x_37);
lean::cnstr_set(x_119, 3, x_113);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_118);
x_120 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set(x_120, 1, x_110);
lean::cnstr_set(x_120, 2, x_111);
lean::cnstr_set(x_120, 3, x_112);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_118);
lean::cnstr_set(x_1, 3, x_120);
lean::cnstr_set(x_1, 2, x_115);
lean::cnstr_set(x_1, 1, x_114);
lean::cnstr_set(x_1, 0, x_119);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
obj* x_121; 
x_121 = lean::cnstr_get(x_46, 3);
lean::inc(x_121);
if (lean::obj_tag(x_121) == 0)
{
uint8 x_122; 
x_122 = !lean::is_exclusive(x_46);
if (x_122 == 0)
{
obj* x_123; obj* x_124; uint8 x_125; 
x_123 = lean::cnstr_get(x_46, 3);
lean::dec(x_123);
x_124 = lean::cnstr_get(x_46, 0);
lean::dec(x_124);
x_125 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_125);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
obj* x_126; obj* x_127; uint8 x_128; obj* x_129; 
x_126 = lean::cnstr_get(x_46, 1);
x_127 = lean::cnstr_get(x_46, 2);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_46);
x_128 = 0;
x_129 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_129, 0, x_47);
lean::cnstr_set(x_129, 1, x_126);
lean::cnstr_set(x_129, 2, x_127);
lean::cnstr_set(x_129, 3, x_121);
lean::cnstr_set_scalar(x_129, sizeof(void*)*4, x_128);
lean::cnstr_set(x_1, 3, x_129);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8 x_130; 
x_130 = lean::cnstr_get_scalar<uint8>(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8 x_131; 
lean::free_heap_obj(x_1);
x_131 = !lean::is_exclusive(x_46);
if (x_131 == 0)
{
obj* x_132; obj* x_133; uint8 x_134; 
x_132 = lean::cnstr_get(x_46, 3);
lean::dec(x_132);
x_133 = lean::cnstr_get(x_46, 0);
lean::dec(x_133);
x_134 = !lean::is_exclusive(x_121);
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; uint8 x_139; 
x_135 = lean::cnstr_get(x_121, 0);
x_136 = lean::cnstr_get(x_121, 1);
x_137 = lean::cnstr_get(x_121, 2);
x_138 = lean::cnstr_get(x_121, 3);
lean::inc(x_47);
lean::cnstr_set(x_121, 3, x_47);
lean::cnstr_set(x_121, 2, x_37);
lean::cnstr_set(x_121, 1, x_36);
lean::cnstr_set(x_121, 0, x_35);
x_139 = !lean::is_exclusive(x_47);
if (x_139 == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
x_140 = lean::cnstr_get(x_47, 3);
lean::dec(x_140);
x_141 = lean::cnstr_get(x_47, 2);
lean::dec(x_141);
x_142 = lean::cnstr_get(x_47, 1);
lean::dec(x_142);
x_143 = lean::cnstr_get(x_47, 0);
lean::dec(x_143);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
lean::cnstr_set(x_47, 3, x_138);
lean::cnstr_set(x_47, 2, x_137);
lean::cnstr_set(x_47, 1, x_136);
lean::cnstr_set(x_47, 0, x_135);
lean::cnstr_set(x_46, 3, x_47);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
obj* x_144; 
lean::dec(x_47);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_95);
x_144 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_144, 0, x_135);
lean::cnstr_set(x_144, 1, x_136);
lean::cnstr_set(x_144, 2, x_137);
lean::cnstr_set(x_144, 3, x_138);
lean::cnstr_set_scalar(x_144, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_144);
lean::cnstr_set(x_46, 0, x_121);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_121, 0);
x_146 = lean::cnstr_get(x_121, 1);
x_147 = lean::cnstr_get(x_121, 2);
x_148 = lean::cnstr_get(x_121, 3);
lean::inc(x_148);
lean::inc(x_147);
lean::inc(x_146);
lean::inc(x_145);
lean::dec(x_121);
lean::inc(x_47);
x_149 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_149, 0, x_35);
lean::cnstr_set(x_149, 1, x_36);
lean::cnstr_set(x_149, 2, x_37);
lean::cnstr_set(x_149, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_150 = x_47;
} else {
 lean::dec_ref(x_47);
 x_150 = lean::box(0);
}
lean::cnstr_set_scalar(x_149, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_145);
lean::cnstr_set(x_151, 1, x_146);
lean::cnstr_set(x_151, 2, x_147);
lean::cnstr_set(x_151, 3, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_95);
lean::cnstr_set(x_46, 3, x_151);
lean::cnstr_set(x_46, 0, x_149);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
x_152 = lean::cnstr_get(x_46, 1);
x_153 = lean::cnstr_get(x_46, 2);
lean::inc(x_153);
lean::inc(x_152);
lean::dec(x_46);
x_154 = lean::cnstr_get(x_121, 0);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_121, 1);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_121, 2);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_121, 3);
lean::inc(x_157);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 lean::cnstr_release(x_121, 2);
 lean::cnstr_release(x_121, 3);
 x_158 = x_121;
} else {
 lean::dec_ref(x_121);
 x_158 = lean::box(0);
}
lean::inc(x_47);
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_35);
lean::cnstr_set(x_159, 1, x_36);
lean::cnstr_set(x_159, 2, x_37);
lean::cnstr_set(x_159, 3, x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_160 = x_47;
} else {
 lean::dec_ref(x_47);
 x_160 = lean::box(0);
}
lean::cnstr_set_scalar(x_159, sizeof(void*)*4, x_95);
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_154);
lean::cnstr_set(x_161, 1, x_155);
lean::cnstr_set(x_161, 2, x_156);
lean::cnstr_set(x_161, 3, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*4, x_95);
x_162 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_162, 0, x_159);
lean::cnstr_set(x_162, 1, x_152);
lean::cnstr_set(x_162, 2, x_153);
lean::cnstr_set(x_162, 3, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8 x_163; 
x_163 = !lean::is_exclusive(x_46);
if (x_163 == 0)
{
obj* x_164; obj* x_165; uint8 x_166; 
x_164 = lean::cnstr_get(x_46, 3);
lean::dec(x_164);
x_165 = lean::cnstr_get(x_46, 0);
lean::dec(x_165);
x_166 = !lean::is_exclusive(x_47);
if (x_166 == 0)
{
uint8 x_167; 
lean::cnstr_set_scalar(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_167);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; uint8 x_173; 
x_168 = lean::cnstr_get(x_47, 0);
x_169 = lean::cnstr_get(x_47, 1);
x_170 = lean::cnstr_get(x_47, 2);
x_171 = lean::cnstr_get(x_47, 3);
lean::inc(x_171);
lean::inc(x_170);
lean::inc(x_169);
lean::inc(x_168);
lean::dec(x_47);
x_172 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_172, 0, x_168);
lean::cnstr_set(x_172, 1, x_169);
lean::cnstr_set(x_172, 2, x_170);
lean::cnstr_set(x_172, 3, x_171);
lean::cnstr_set_scalar(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean::cnstr_set(x_46, 0, x_172);
lean::cnstr_set_scalar(x_46, sizeof(void*)*4, x_173);
lean::cnstr_set(x_1, 3, x_46);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; uint8 x_182; obj* x_183; 
x_174 = lean::cnstr_get(x_46, 1);
x_175 = lean::cnstr_get(x_46, 2);
lean::inc(x_175);
lean::inc(x_174);
lean::dec(x_46);
x_176 = lean::cnstr_get(x_47, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_47, 1);
lean::inc(x_177);
x_178 = lean::cnstr_get(x_47, 2);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_47, 3);
lean::inc(x_179);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 lean::cnstr_release(x_47, 3);
 x_180 = x_47;
} else {
 lean::dec_ref(x_47);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_176);
lean::cnstr_set(x_181, 1, x_177);
lean::cnstr_set(x_181, 2, x_178);
lean::cnstr_set(x_181, 3, x_179);
lean::cnstr_set_scalar(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_183, 0, x_181);
lean::cnstr_set(x_183, 1, x_174);
lean::cnstr_set(x_183, 2, x_175);
lean::cnstr_set(x_183, 3, x_121);
lean::cnstr_set_scalar(x_183, sizeof(void*)*4, x_182);
lean::cnstr_set(x_1, 3, x_183);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_130);
return x_1;
}
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
uint8 x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
obj* x_185; 
x_185 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_35, x_2, x_3);
lean::cnstr_set(x_1, 0, x_185);
return x_1;
}
else
{
obj* x_186; 
x_186 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_35, x_2, x_3);
if (lean::obj_tag(x_186) == 0)
{
lean::free_heap_obj(x_1);
lean::dec(x_38);
lean::dec(x_37);
lean::dec(x_36);
return x_186;
}
else
{
obj* x_187; 
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; 
x_188 = lean::cnstr_get(x_186, 3);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
uint8 x_189; 
x_189 = !lean::is_exclusive(x_186);
if (x_189 == 0)
{
obj* x_190; obj* x_191; uint8 x_192; uint8 x_193; 
x_190 = lean::cnstr_get(x_186, 3);
lean::dec(x_190);
x_191 = lean::cnstr_get(x_186, 0);
lean::dec(x_191);
x_192 = 0;
lean::cnstr_set(x_186, 0, x_188);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
obj* x_194; obj* x_195; uint8 x_196; obj* x_197; uint8 x_198; 
x_194 = lean::cnstr_get(x_186, 1);
x_195 = lean::cnstr_get(x_186, 2);
lean::inc(x_195);
lean::inc(x_194);
lean::dec(x_186);
x_196 = 0;
x_197 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_197, 0, x_188);
lean::cnstr_set(x_197, 1, x_194);
lean::cnstr_set(x_197, 2, x_195);
lean::cnstr_set(x_197, 3, x_188);
lean::cnstr_set_scalar(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean::cnstr_set(x_1, 0, x_197);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8 x_199; 
x_199 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8 x_200; 
x_200 = !lean::is_exclusive(x_186);
if (x_200 == 0)
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; uint8 x_205; 
x_201 = lean::cnstr_get(x_186, 1);
x_202 = lean::cnstr_get(x_186, 2);
x_203 = lean::cnstr_get(x_186, 3);
lean::dec(x_203);
x_204 = lean::cnstr_get(x_186, 0);
lean::dec(x_204);
x_205 = !lean::is_exclusive(x_188);
if (x_205 == 0)
{
obj* x_206; obj* x_207; obj* x_208; obj* x_209; uint8 x_210; 
x_206 = lean::cnstr_get(x_188, 0);
x_207 = lean::cnstr_get(x_188, 1);
x_208 = lean::cnstr_get(x_188, 2);
x_209 = lean::cnstr_get(x_188, 3);
x_210 = 1;
lean::cnstr_set(x_188, 3, x_206);
lean::cnstr_set(x_188, 2, x_202);
lean::cnstr_set(x_188, 1, x_201);
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set_scalar(x_188, sizeof(void*)*4, x_210);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_209);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_210);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_208);
lean::cnstr_set(x_1, 1, x_207);
lean::cnstr_set(x_1, 0, x_188);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_211; obj* x_212; obj* x_213; obj* x_214; uint8 x_215; obj* x_216; 
x_211 = lean::cnstr_get(x_188, 0);
x_212 = lean::cnstr_get(x_188, 1);
x_213 = lean::cnstr_get(x_188, 2);
x_214 = lean::cnstr_get(x_188, 3);
lean::inc(x_214);
lean::inc(x_213);
lean::inc(x_212);
lean::inc(x_211);
lean::dec(x_188);
x_215 = 1;
x_216 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_216, 0, x_187);
lean::cnstr_set(x_216, 1, x_201);
lean::cnstr_set(x_216, 2, x_202);
lean::cnstr_set(x_216, 3, x_211);
lean::cnstr_set_scalar(x_216, sizeof(void*)*4, x_215);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_214);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_215);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_213);
lean::cnstr_set(x_1, 1, x_212);
lean::cnstr_set(x_1, 0, x_216);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; uint8 x_224; obj* x_225; obj* x_226; 
x_217 = lean::cnstr_get(x_186, 1);
x_218 = lean::cnstr_get(x_186, 2);
lean::inc(x_218);
lean::inc(x_217);
lean::dec(x_186);
x_219 = lean::cnstr_get(x_188, 0);
lean::inc(x_219);
x_220 = lean::cnstr_get(x_188, 1);
lean::inc(x_220);
x_221 = lean::cnstr_get(x_188, 2);
lean::inc(x_221);
x_222 = lean::cnstr_get(x_188, 3);
lean::inc(x_222);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_release(x_188, 1);
 lean::cnstr_release(x_188, 2);
 lean::cnstr_release(x_188, 3);
 x_223 = x_188;
} else {
 lean::dec_ref(x_188);
 x_223 = lean::box(0);
}
x_224 = 1;
if (lean::is_scalar(x_223)) {
 x_225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_225 = x_223;
}
lean::cnstr_set(x_225, 0, x_187);
lean::cnstr_set(x_225, 1, x_217);
lean::cnstr_set(x_225, 2, x_218);
lean::cnstr_set(x_225, 3, x_219);
lean::cnstr_set_scalar(x_225, sizeof(void*)*4, x_224);
x_226 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set(x_226, 1, x_36);
lean::cnstr_set(x_226, 2, x_37);
lean::cnstr_set(x_226, 3, x_38);
lean::cnstr_set_scalar(x_226, sizeof(void*)*4, x_224);
lean::cnstr_set(x_1, 3, x_226);
lean::cnstr_set(x_1, 2, x_221);
lean::cnstr_set(x_1, 1, x_220);
lean::cnstr_set(x_1, 0, x_225);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8 x_227; 
x_227 = !lean::is_exclusive(x_186);
if (x_227 == 0)
{
obj* x_228; obj* x_229; uint8 x_230; 
x_228 = lean::cnstr_get(x_186, 3);
lean::dec(x_228);
x_229 = lean::cnstr_get(x_186, 0);
lean::dec(x_229);
x_230 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_230);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
obj* x_231; obj* x_232; uint8 x_233; obj* x_234; 
x_231 = lean::cnstr_get(x_186, 1);
x_232 = lean::cnstr_get(x_186, 2);
lean::inc(x_232);
lean::inc(x_231);
lean::dec(x_186);
x_233 = 0;
x_234 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_234, 0, x_187);
lean::cnstr_set(x_234, 1, x_231);
lean::cnstr_set(x_234, 2, x_232);
lean::cnstr_set(x_234, 3, x_188);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 0, x_234);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8 x_235; 
x_235 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8 x_236; 
x_236 = !lean::is_exclusive(x_186);
if (x_236 == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; uint8 x_241; 
x_237 = lean::cnstr_get(x_186, 1);
x_238 = lean::cnstr_get(x_186, 2);
x_239 = lean::cnstr_get(x_186, 3);
x_240 = lean::cnstr_get(x_186, 0);
lean::dec(x_240);
x_241 = !lean::is_exclusive(x_187);
if (x_241 == 0)
{
uint8 x_242; 
x_242 = 1;
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_242);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_242);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_187);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; uint8 x_247; obj* x_248; 
x_243 = lean::cnstr_get(x_187, 0);
x_244 = lean::cnstr_get(x_187, 1);
x_245 = lean::cnstr_get(x_187, 2);
x_246 = lean::cnstr_get(x_187, 3);
lean::inc(x_246);
lean::inc(x_245);
lean::inc(x_244);
lean::inc(x_243);
lean::dec(x_187);
x_247 = 1;
x_248 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_248, 0, x_243);
lean::cnstr_set(x_248, 1, x_244);
lean::cnstr_set(x_248, 2, x_245);
lean::cnstr_set(x_248, 3, x_246);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_247);
lean::cnstr_set(x_186, 3, x_38);
lean::cnstr_set(x_186, 2, x_37);
lean::cnstr_set(x_186, 1, x_36);
lean::cnstr_set(x_186, 0, x_239);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_247);
lean::cnstr_set(x_1, 3, x_186);
lean::cnstr_set(x_1, 2, x_238);
lean::cnstr_set(x_1, 1, x_237);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; uint8 x_257; obj* x_258; obj* x_259; 
x_249 = lean::cnstr_get(x_186, 1);
x_250 = lean::cnstr_get(x_186, 2);
x_251 = lean::cnstr_get(x_186, 3);
lean::inc(x_251);
lean::inc(x_250);
lean::inc(x_249);
lean::dec(x_186);
x_252 = lean::cnstr_get(x_187, 0);
lean::inc(x_252);
x_253 = lean::cnstr_get(x_187, 1);
lean::inc(x_253);
x_254 = lean::cnstr_get(x_187, 2);
lean::inc(x_254);
x_255 = lean::cnstr_get(x_187, 3);
lean::inc(x_255);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_256 = x_187;
} else {
 lean::dec_ref(x_187);
 x_256 = lean::box(0);
}
x_257 = 1;
if (lean::is_scalar(x_256)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_256;
}
lean::cnstr_set(x_258, 0, x_252);
lean::cnstr_set(x_258, 1, x_253);
lean::cnstr_set(x_258, 2, x_254);
lean::cnstr_set(x_258, 3, x_255);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_257);
x_259 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_259, 0, x_251);
lean::cnstr_set(x_259, 1, x_36);
lean::cnstr_set(x_259, 2, x_37);
lean::cnstr_set(x_259, 3, x_38);
lean::cnstr_set_scalar(x_259, sizeof(void*)*4, x_257);
lean::cnstr_set(x_1, 3, x_259);
lean::cnstr_set(x_1, 2, x_250);
lean::cnstr_set(x_1, 1, x_249);
lean::cnstr_set(x_1, 0, x_258);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_186, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
uint8 x_261; 
x_261 = !lean::is_exclusive(x_186);
if (x_261 == 0)
{
obj* x_262; obj* x_263; uint8 x_264; 
x_262 = lean::cnstr_get(x_186, 3);
lean::dec(x_262);
x_263 = lean::cnstr_get(x_186, 0);
lean::dec(x_263);
x_264 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_264);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
obj* x_265; obj* x_266; uint8 x_267; obj* x_268; 
x_265 = lean::cnstr_get(x_186, 1);
x_266 = lean::cnstr_get(x_186, 2);
lean::inc(x_266);
lean::inc(x_265);
lean::dec(x_186);
x_267 = 0;
x_268 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_268, 0, x_187);
lean::cnstr_set(x_268, 1, x_265);
lean::cnstr_set(x_268, 2, x_266);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
lean::cnstr_set(x_1, 0, x_268);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8 x_269; 
x_269 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8 x_270; 
lean::free_heap_obj(x_1);
x_270 = !lean::is_exclusive(x_186);
if (x_270 == 0)
{
obj* x_271; obj* x_272; obj* x_273; obj* x_274; uint8 x_275; 
x_271 = lean::cnstr_get(x_186, 1);
x_272 = lean::cnstr_get(x_186, 2);
x_273 = lean::cnstr_get(x_186, 3);
lean::dec(x_273);
x_274 = lean::cnstr_get(x_186, 0);
lean::dec(x_274);
x_275 = !lean::is_exclusive(x_260);
if (x_275 == 0)
{
obj* x_276; obj* x_277; obj* x_278; obj* x_279; uint8 x_280; 
x_276 = lean::cnstr_get(x_260, 0);
x_277 = lean::cnstr_get(x_260, 1);
x_278 = lean::cnstr_get(x_260, 2);
x_279 = lean::cnstr_get(x_260, 3);
lean::inc(x_187);
lean::cnstr_set(x_260, 3, x_276);
lean::cnstr_set(x_260, 2, x_272);
lean::cnstr_set(x_260, 1, x_271);
lean::cnstr_set(x_260, 0, x_187);
x_280 = !lean::is_exclusive(x_187);
if (x_280 == 0)
{
obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
x_281 = lean::cnstr_get(x_187, 3);
lean::dec(x_281);
x_282 = lean::cnstr_get(x_187, 2);
lean::dec(x_282);
x_283 = lean::cnstr_get(x_187, 1);
lean::dec(x_283);
x_284 = lean::cnstr_get(x_187, 0);
lean::dec(x_284);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
lean::cnstr_set(x_187, 3, x_38);
lean::cnstr_set(x_187, 2, x_37);
lean::cnstr_set(x_187, 1, x_36);
lean::cnstr_set(x_187, 0, x_279);
lean::cnstr_set(x_186, 3, x_187);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
obj* x_285; 
lean::dec(x_187);
lean::cnstr_set_scalar(x_260, sizeof(void*)*4, x_235);
x_285 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_285, 0, x_279);
lean::cnstr_set(x_285, 1, x_36);
lean::cnstr_set(x_285, 2, x_37);
lean::cnstr_set(x_285, 3, x_38);
lean::cnstr_set_scalar(x_285, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_285);
lean::cnstr_set(x_186, 2, x_278);
lean::cnstr_set(x_186, 1, x_277);
lean::cnstr_set(x_186, 0, x_260);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
x_286 = lean::cnstr_get(x_260, 0);
x_287 = lean::cnstr_get(x_260, 1);
x_288 = lean::cnstr_get(x_260, 2);
x_289 = lean::cnstr_get(x_260, 3);
lean::inc(x_289);
lean::inc(x_288);
lean::inc(x_287);
lean::inc(x_286);
lean::dec(x_260);
lean::inc(x_187);
x_290 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_290, 0, x_187);
lean::cnstr_set(x_290, 1, x_271);
lean::cnstr_set(x_290, 2, x_272);
lean::cnstr_set(x_290, 3, x_286);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_291 = x_187;
} else {
 lean::dec_ref(x_187);
 x_291 = lean::box(0);
}
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_289);
lean::cnstr_set(x_292, 1, x_36);
lean::cnstr_set(x_292, 2, x_37);
lean::cnstr_set(x_292, 3, x_38);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_235);
lean::cnstr_set(x_186, 3, x_292);
lean::cnstr_set(x_186, 2, x_288);
lean::cnstr_set(x_186, 1, x_287);
lean::cnstr_set(x_186, 0, x_290);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_293 = lean::cnstr_get(x_186, 1);
x_294 = lean::cnstr_get(x_186, 2);
lean::inc(x_294);
lean::inc(x_293);
lean::dec(x_186);
x_295 = lean::cnstr_get(x_260, 0);
lean::inc(x_295);
x_296 = lean::cnstr_get(x_260, 1);
lean::inc(x_296);
x_297 = lean::cnstr_get(x_260, 2);
lean::inc(x_297);
x_298 = lean::cnstr_get(x_260, 3);
lean::inc(x_298);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_release(x_260, 0);
 lean::cnstr_release(x_260, 1);
 lean::cnstr_release(x_260, 2);
 lean::cnstr_release(x_260, 3);
 x_299 = x_260;
} else {
 lean::dec_ref(x_260);
 x_299 = lean::box(0);
}
lean::inc(x_187);
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_187);
lean::cnstr_set(x_300, 1, x_293);
lean::cnstr_set(x_300, 2, x_294);
lean::cnstr_set(x_300, 3, x_295);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_301 = x_187;
} else {
 lean::dec_ref(x_187);
 x_301 = lean::box(0);
}
lean::cnstr_set_scalar(x_300, sizeof(void*)*4, x_235);
if (lean::is_scalar(x_301)) {
 x_302 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_302 = x_301;
}
lean::cnstr_set(x_302, 0, x_298);
lean::cnstr_set(x_302, 1, x_36);
lean::cnstr_set(x_302, 2, x_37);
lean::cnstr_set(x_302, 3, x_38);
lean::cnstr_set_scalar(x_302, sizeof(void*)*4, x_235);
x_303 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_303, 0, x_300);
lean::cnstr_set(x_303, 1, x_296);
lean::cnstr_set(x_303, 2, x_297);
lean::cnstr_set(x_303, 3, x_302);
lean::cnstr_set_scalar(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8 x_304; 
x_304 = !lean::is_exclusive(x_186);
if (x_304 == 0)
{
obj* x_305; obj* x_306; uint8 x_307; 
x_305 = lean::cnstr_get(x_186, 3);
lean::dec(x_305);
x_306 = lean::cnstr_get(x_186, 0);
lean::dec(x_306);
x_307 = !lean::is_exclusive(x_187);
if (x_307 == 0)
{
uint8 x_308; 
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_308);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; uint8 x_314; 
x_309 = lean::cnstr_get(x_187, 0);
x_310 = lean::cnstr_get(x_187, 1);
x_311 = lean::cnstr_get(x_187, 2);
x_312 = lean::cnstr_get(x_187, 3);
lean::inc(x_312);
lean::inc(x_311);
lean::inc(x_310);
lean::inc(x_309);
lean::dec(x_187);
x_313 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_313, 0, x_309);
lean::cnstr_set(x_313, 1, x_310);
lean::cnstr_set(x_313, 2, x_311);
lean::cnstr_set(x_313, 3, x_312);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean::cnstr_set(x_186, 0, x_313);
lean::cnstr_set_scalar(x_186, sizeof(void*)*4, x_314);
lean::cnstr_set(x_1, 0, x_186);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; uint8 x_323; obj* x_324; 
x_315 = lean::cnstr_get(x_186, 1);
x_316 = lean::cnstr_get(x_186, 2);
lean::inc(x_316);
lean::inc(x_315);
lean::dec(x_186);
x_317 = lean::cnstr_get(x_187, 0);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_187, 1);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_187, 2);
lean::inc(x_319);
x_320 = lean::cnstr_get(x_187, 3);
lean::inc(x_320);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_release(x_187, 1);
 lean::cnstr_release(x_187, 2);
 lean::cnstr_release(x_187, 3);
 x_321 = x_187;
} else {
 lean::dec_ref(x_187);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_317);
lean::cnstr_set(x_322, 1, x_318);
lean::cnstr_set(x_322, 2, x_319);
lean::cnstr_set(x_322, 3, x_320);
lean::cnstr_set_scalar(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_322);
lean::cnstr_set(x_324, 1, x_315);
lean::cnstr_set(x_324, 2, x_316);
lean::cnstr_set(x_324, 3, x_260);
lean::cnstr_set_scalar(x_324, sizeof(void*)*4, x_323);
lean::cnstr_set(x_1, 0, x_324);
lean::cnstr_set_scalar(x_1, sizeof(void*)*4, x_269);
return x_1;
}
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
obj* x_325; obj* x_326; obj* x_327; obj* x_328; uint32 x_329; uint8 x_330; 
x_325 = lean::cnstr_get(x_1, 0);
x_326 = lean::cnstr_get(x_1, 1);
x_327 = lean::cnstr_get(x_1, 2);
x_328 = lean::cnstr_get(x_1, 3);
lean::inc(x_328);
lean::inc(x_327);
lean::inc(x_326);
lean::inc(x_325);
lean::dec(x_1);
x_329 = lean::unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32 x_331; uint8 x_332; 
x_331 = lean::unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
obj* x_333; obj* x_334; 
lean::dec(x_327);
lean::dec(x_326);
x_333 = lean::box_uint32(x_2);
x_334 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_334, 0, x_325);
lean::cnstr_set(x_334, 1, x_333);
lean::cnstr_set(x_334, 2, x_3);
lean::cnstr_set(x_334, 3, x_328);
lean::cnstr_set_scalar(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8 x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
obj* x_336; obj* x_337; 
x_336 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_328, x_2, x_3);
x_337 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_337, 0, x_325);
lean::cnstr_set(x_337, 1, x_326);
lean::cnstr_set(x_337, 2, x_327);
lean::cnstr_set(x_337, 3, x_336);
lean::cnstr_set_scalar(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
obj* x_338; 
x_338 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_328, x_2, x_3);
if (lean::obj_tag(x_338) == 0)
{
lean::dec(x_327);
lean::dec(x_326);
lean::dec(x_325);
return x_338;
}
else
{
obj* x_339; 
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
if (lean::obj_tag(x_339) == 0)
{
obj* x_340; 
x_340 = lean::cnstr_get(x_338, 3);
lean::inc(x_340);
if (lean::obj_tag(x_340) == 0)
{
obj* x_341; obj* x_342; obj* x_343; uint8 x_344; obj* x_345; uint8 x_346; obj* x_347; 
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
x_342 = lean::cnstr_get(x_338, 2);
lean::inc(x_342);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_343 = x_338;
} else {
 lean::dec_ref(x_338);
 x_343 = lean::box(0);
}
x_344 = 0;
if (lean::is_scalar(x_343)) {
 x_345 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_345 = x_343;
}
lean::cnstr_set(x_345, 0, x_340);
lean::cnstr_set(x_345, 1, x_341);
lean::cnstr_set(x_345, 2, x_342);
lean::cnstr_set(x_345, 3, x_340);
lean::cnstr_set_scalar(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_347, 0, x_325);
lean::cnstr_set(x_347, 1, x_326);
lean::cnstr_set(x_347, 2, x_327);
lean::cnstr_set(x_347, 3, x_345);
lean::cnstr_set_scalar(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8 x_348; 
x_348 = lean::cnstr_get_scalar<uint8>(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; uint8 x_357; obj* x_358; obj* x_359; obj* x_360; 
x_349 = lean::cnstr_get(x_338, 1);
lean::inc(x_349);
x_350 = lean::cnstr_get(x_338, 2);
lean::inc(x_350);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_351 = x_338;
} else {
 lean::dec_ref(x_338);
 x_351 = lean::box(0);
}
x_352 = lean::cnstr_get(x_340, 0);
lean::inc(x_352);
x_353 = lean::cnstr_get(x_340, 1);
lean::inc(x_353);
x_354 = lean::cnstr_get(x_340, 2);
lean::inc(x_354);
x_355 = lean::cnstr_get(x_340, 3);
lean::inc(x_355);
if (lean::is_exclusive(x_340)) {
 lean::cnstr_release(x_340, 0);
 lean::cnstr_release(x_340, 1);
 lean::cnstr_release(x_340, 2);
 lean::cnstr_release(x_340, 3);
 x_356 = x_340;
} else {
 lean::dec_ref(x_340);
 x_356 = lean::box(0);
}
x_357 = 1;
if (lean::is_scalar(x_356)) {
 x_358 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_358 = x_356;
}
lean::cnstr_set(x_358, 0, x_325);
lean::cnstr_set(x_358, 1, x_326);
lean::cnstr_set(x_358, 2, x_327);
lean::cnstr_set(x_358, 3, x_339);
lean::cnstr_set_scalar(x_358, sizeof(void*)*4, x_357);
if (lean::is_scalar(x_351)) {
 x_359 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_359 = x_351;
}
lean::cnstr_set(x_359, 0, x_352);
lean::cnstr_set(x_359, 1, x_353);
lean::cnstr_set(x_359, 2, x_354);
lean::cnstr_set(x_359, 3, x_355);
lean::cnstr_set_scalar(x_359, sizeof(void*)*4, x_357);
x_360 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_360, 0, x_358);
lean::cnstr_set(x_360, 1, x_349);
lean::cnstr_set(x_360, 2, x_350);
lean::cnstr_set(x_360, 3, x_359);
lean::cnstr_set_scalar(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
obj* x_361; obj* x_362; obj* x_363; uint8 x_364; obj* x_365; obj* x_366; 
x_361 = lean::cnstr_get(x_338, 1);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_338, 2);
lean::inc(x_362);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_363 = x_338;
} else {
 lean::dec_ref(x_338);
 x_363 = lean::box(0);
}
x_364 = 0;
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_339);
lean::cnstr_set(x_365, 1, x_361);
lean::cnstr_set(x_365, 2, x_362);
lean::cnstr_set(x_365, 3, x_340);
lean::cnstr_set_scalar(x_365, sizeof(void*)*4, x_364);
x_366 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_366, 0, x_325);
lean::cnstr_set(x_366, 1, x_326);
lean::cnstr_set(x_366, 2, x_327);
lean::cnstr_set(x_366, 3, x_365);
lean::cnstr_set_scalar(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8 x_367; 
x_367 = lean::cnstr_get_scalar<uint8>(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; uint8 x_377; obj* x_378; obj* x_379; obj* x_380; 
x_368 = lean::cnstr_get(x_338, 1);
lean::inc(x_368);
x_369 = lean::cnstr_get(x_338, 2);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_338, 3);
lean::inc(x_370);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_371 = x_338;
} else {
 lean::dec_ref(x_338);
 x_371 = lean::box(0);
}
x_372 = lean::cnstr_get(x_339, 0);
lean::inc(x_372);
x_373 = lean::cnstr_get(x_339, 1);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_339, 2);
lean::inc(x_374);
x_375 = lean::cnstr_get(x_339, 3);
lean::inc(x_375);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_376 = x_339;
} else {
 lean::dec_ref(x_339);
 x_376 = lean::box(0);
}
x_377 = 1;
if (lean::is_scalar(x_376)) {
 x_378 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_378 = x_376;
}
lean::cnstr_set(x_378, 0, x_325);
lean::cnstr_set(x_378, 1, x_326);
lean::cnstr_set(x_378, 2, x_327);
lean::cnstr_set(x_378, 3, x_372);
lean::cnstr_set_scalar(x_378, sizeof(void*)*4, x_377);
if (lean::is_scalar(x_371)) {
 x_379 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_379 = x_371;
}
lean::cnstr_set(x_379, 0, x_375);
lean::cnstr_set(x_379, 1, x_368);
lean::cnstr_set(x_379, 2, x_369);
lean::cnstr_set(x_379, 3, x_370);
lean::cnstr_set_scalar(x_379, sizeof(void*)*4, x_377);
x_380 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_380, 0, x_378);
lean::cnstr_set(x_380, 1, x_373);
lean::cnstr_set(x_380, 2, x_374);
lean::cnstr_set(x_380, 3, x_379);
lean::cnstr_set_scalar(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
obj* x_381; 
x_381 = lean::cnstr_get(x_338, 3);
lean::inc(x_381);
if (lean::obj_tag(x_381) == 0)
{
obj* x_382; obj* x_383; obj* x_384; uint8 x_385; obj* x_386; obj* x_387; 
x_382 = lean::cnstr_get(x_338, 1);
lean::inc(x_382);
x_383 = lean::cnstr_get(x_338, 2);
lean::inc(x_383);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_384 = x_338;
} else {
 lean::dec_ref(x_338);
 x_384 = lean::box(0);
}
x_385 = 0;
if (lean::is_scalar(x_384)) {
 x_386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_386 = x_384;
}
lean::cnstr_set(x_386, 0, x_339);
lean::cnstr_set(x_386, 1, x_382);
lean::cnstr_set(x_386, 2, x_383);
lean::cnstr_set(x_386, 3, x_381);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_385);
x_387 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_387, 0, x_325);
lean::cnstr_set(x_387, 1, x_326);
lean::cnstr_set(x_387, 2, x_327);
lean::cnstr_set(x_387, 3, x_386);
lean::cnstr_set_scalar(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8 x_388; 
x_388 = lean::cnstr_get_scalar<uint8>(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; 
x_389 = lean::cnstr_get(x_338, 1);
lean::inc(x_389);
x_390 = lean::cnstr_get(x_338, 2);
lean::inc(x_390);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_391 = x_338;
} else {
 lean::dec_ref(x_338);
 x_391 = lean::box(0);
}
x_392 = lean::cnstr_get(x_381, 0);
lean::inc(x_392);
x_393 = lean::cnstr_get(x_381, 1);
lean::inc(x_393);
x_394 = lean::cnstr_get(x_381, 2);
lean::inc(x_394);
x_395 = lean::cnstr_get(x_381, 3);
lean::inc(x_395);
if (lean::is_exclusive(x_381)) {
 lean::cnstr_release(x_381, 0);
 lean::cnstr_release(x_381, 1);
 lean::cnstr_release(x_381, 2);
 lean::cnstr_release(x_381, 3);
 x_396 = x_381;
} else {
 lean::dec_ref(x_381);
 x_396 = lean::box(0);
}
lean::inc(x_339);
if (lean::is_scalar(x_396)) {
 x_397 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_397 = x_396;
}
lean::cnstr_set(x_397, 0, x_325);
lean::cnstr_set(x_397, 1, x_326);
lean::cnstr_set(x_397, 2, x_327);
lean::cnstr_set(x_397, 3, x_339);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_398 = x_339;
} else {
 lean::dec_ref(x_339);
 x_398 = lean::box(0);
}
lean::cnstr_set_scalar(x_397, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_392);
lean::cnstr_set(x_399, 1, x_393);
lean::cnstr_set(x_399, 2, x_394);
lean::cnstr_set(x_399, 3, x_395);
lean::cnstr_set_scalar(x_399, sizeof(void*)*4, x_367);
if (lean::is_scalar(x_391)) {
 x_400 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_400 = x_391;
}
lean::cnstr_set(x_400, 0, x_397);
lean::cnstr_set(x_400, 1, x_389);
lean::cnstr_set(x_400, 2, x_390);
lean::cnstr_set(x_400, 3, x_399);
lean::cnstr_set_scalar(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_409; uint8 x_410; obj* x_411; obj* x_412; 
x_401 = lean::cnstr_get(x_338, 1);
lean::inc(x_401);
x_402 = lean::cnstr_get(x_338, 2);
lean::inc(x_402);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 lean::cnstr_release(x_338, 1);
 lean::cnstr_release(x_338, 2);
 lean::cnstr_release(x_338, 3);
 x_403 = x_338;
} else {
 lean::dec_ref(x_338);
 x_403 = lean::box(0);
}
x_404 = lean::cnstr_get(x_339, 0);
lean::inc(x_404);
x_405 = lean::cnstr_get(x_339, 1);
lean::inc(x_405);
x_406 = lean::cnstr_get(x_339, 2);
lean::inc(x_406);
x_407 = lean::cnstr_get(x_339, 3);
lean::inc(x_407);
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 lean::cnstr_release(x_339, 1);
 lean::cnstr_release(x_339, 2);
 lean::cnstr_release(x_339, 3);
 x_408 = x_339;
} else {
 lean::dec_ref(x_339);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_404);
lean::cnstr_set(x_409, 1, x_405);
lean::cnstr_set(x_409, 2, x_406);
lean::cnstr_set(x_409, 3, x_407);
lean::cnstr_set_scalar(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean::is_scalar(x_403)) {
 x_411 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_411 = x_403;
}
lean::cnstr_set(x_411, 0, x_409);
lean::cnstr_set(x_411, 1, x_401);
lean::cnstr_set(x_411, 2, x_402);
lean::cnstr_set(x_411, 3, x_381);
lean::cnstr_set_scalar(x_411, sizeof(void*)*4, x_410);
x_412 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_412, 0, x_325);
lean::cnstr_set(x_412, 1, x_326);
lean::cnstr_set(x_412, 2, x_327);
lean::cnstr_set(x_412, 3, x_411);
lean::cnstr_set_scalar(x_412, sizeof(void*)*4, x_388);
return x_412;
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
uint8 x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
obj* x_414; obj* x_415; 
x_414 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_325, x_2, x_3);
x_415 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_415, 0, x_414);
lean::cnstr_set(x_415, 1, x_326);
lean::cnstr_set(x_415, 2, x_327);
lean::cnstr_set(x_415, 3, x_328);
lean::cnstr_set_scalar(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
obj* x_416; 
x_416 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_325, x_2, x_3);
if (lean::obj_tag(x_416) == 0)
{
lean::dec(x_328);
lean::dec(x_327);
lean::dec(x_326);
return x_416;
}
else
{
obj* x_417; 
x_417 = lean::cnstr_get(x_416, 0);
lean::inc(x_417);
if (lean::obj_tag(x_417) == 0)
{
obj* x_418; 
x_418 = lean::cnstr_get(x_416, 3);
lean::inc(x_418);
if (lean::obj_tag(x_418) == 0)
{
obj* x_419; obj* x_420; obj* x_421; uint8 x_422; obj* x_423; uint8 x_424; obj* x_425; 
x_419 = lean::cnstr_get(x_416, 1);
lean::inc(x_419);
x_420 = lean::cnstr_get(x_416, 2);
lean::inc(x_420);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_421 = x_416;
} else {
 lean::dec_ref(x_416);
 x_421 = lean::box(0);
}
x_422 = 0;
if (lean::is_scalar(x_421)) {
 x_423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_423 = x_421;
}
lean::cnstr_set(x_423, 0, x_418);
lean::cnstr_set(x_423, 1, x_419);
lean::cnstr_set(x_423, 2, x_420);
lean::cnstr_set(x_423, 3, x_418);
lean::cnstr_set_scalar(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_425, 0, x_423);
lean::cnstr_set(x_425, 1, x_326);
lean::cnstr_set(x_425, 2, x_327);
lean::cnstr_set(x_425, 3, x_328);
lean::cnstr_set_scalar(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8 x_426; 
x_426 = lean::cnstr_get_scalar<uint8>(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; obj* x_433; obj* x_434; uint8 x_435; obj* x_436; obj* x_437; obj* x_438; 
x_427 = lean::cnstr_get(x_416, 1);
lean::inc(x_427);
x_428 = lean::cnstr_get(x_416, 2);
lean::inc(x_428);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_429 = x_416;
} else {
 lean::dec_ref(x_416);
 x_429 = lean::box(0);
}
x_430 = lean::cnstr_get(x_418, 0);
lean::inc(x_430);
x_431 = lean::cnstr_get(x_418, 1);
lean::inc(x_431);
x_432 = lean::cnstr_get(x_418, 2);
lean::inc(x_432);
x_433 = lean::cnstr_get(x_418, 3);
lean::inc(x_433);
if (lean::is_exclusive(x_418)) {
 lean::cnstr_release(x_418, 0);
 lean::cnstr_release(x_418, 1);
 lean::cnstr_release(x_418, 2);
 lean::cnstr_release(x_418, 3);
 x_434 = x_418;
} else {
 lean::dec_ref(x_418);
 x_434 = lean::box(0);
}
x_435 = 1;
if (lean::is_scalar(x_434)) {
 x_436 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_436 = x_434;
}
lean::cnstr_set(x_436, 0, x_417);
lean::cnstr_set(x_436, 1, x_427);
lean::cnstr_set(x_436, 2, x_428);
lean::cnstr_set(x_436, 3, x_430);
lean::cnstr_set_scalar(x_436, sizeof(void*)*4, x_435);
if (lean::is_scalar(x_429)) {
 x_437 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_437 = x_429;
}
lean::cnstr_set(x_437, 0, x_433);
lean::cnstr_set(x_437, 1, x_326);
lean::cnstr_set(x_437, 2, x_327);
lean::cnstr_set(x_437, 3, x_328);
lean::cnstr_set_scalar(x_437, sizeof(void*)*4, x_435);
x_438 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_438, 0, x_436);
lean::cnstr_set(x_438, 1, x_431);
lean::cnstr_set(x_438, 2, x_432);
lean::cnstr_set(x_438, 3, x_437);
lean::cnstr_set_scalar(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
obj* x_439; obj* x_440; obj* x_441; uint8 x_442; obj* x_443; obj* x_444; 
x_439 = lean::cnstr_get(x_416, 1);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_416, 2);
lean::inc(x_440);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_441 = x_416;
} else {
 lean::dec_ref(x_416);
 x_441 = lean::box(0);
}
x_442 = 0;
if (lean::is_scalar(x_441)) {
 x_443 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_443 = x_441;
}
lean::cnstr_set(x_443, 0, x_417);
lean::cnstr_set(x_443, 1, x_439);
lean::cnstr_set(x_443, 2, x_440);
lean::cnstr_set(x_443, 3, x_418);
lean::cnstr_set_scalar(x_443, sizeof(void*)*4, x_442);
x_444 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_444, 0, x_443);
lean::cnstr_set(x_444, 1, x_326);
lean::cnstr_set(x_444, 2, x_327);
lean::cnstr_set(x_444, 3, x_328);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8 x_445; 
x_445 = lean::cnstr_get_scalar<uint8>(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; uint8 x_455; obj* x_456; obj* x_457; obj* x_458; 
x_446 = lean::cnstr_get(x_416, 1);
lean::inc(x_446);
x_447 = lean::cnstr_get(x_416, 2);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_416, 3);
lean::inc(x_448);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_449 = x_416;
} else {
 lean::dec_ref(x_416);
 x_449 = lean::box(0);
}
x_450 = lean::cnstr_get(x_417, 0);
lean::inc(x_450);
x_451 = lean::cnstr_get(x_417, 1);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_417, 2);
lean::inc(x_452);
x_453 = lean::cnstr_get(x_417, 3);
lean::inc(x_453);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_454 = x_417;
} else {
 lean::dec_ref(x_417);
 x_454 = lean::box(0);
}
x_455 = 1;
if (lean::is_scalar(x_454)) {
 x_456 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_456 = x_454;
}
lean::cnstr_set(x_456, 0, x_450);
lean::cnstr_set(x_456, 1, x_451);
lean::cnstr_set(x_456, 2, x_452);
lean::cnstr_set(x_456, 3, x_453);
lean::cnstr_set_scalar(x_456, sizeof(void*)*4, x_455);
if (lean::is_scalar(x_449)) {
 x_457 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_457 = x_449;
}
lean::cnstr_set(x_457, 0, x_448);
lean::cnstr_set(x_457, 1, x_326);
lean::cnstr_set(x_457, 2, x_327);
lean::cnstr_set(x_457, 3, x_328);
lean::cnstr_set_scalar(x_457, sizeof(void*)*4, x_455);
x_458 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_458, 0, x_456);
lean::cnstr_set(x_458, 1, x_446);
lean::cnstr_set(x_458, 2, x_447);
lean::cnstr_set(x_458, 3, x_457);
lean::cnstr_set_scalar(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
obj* x_459; 
x_459 = lean::cnstr_get(x_416, 3);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_460; obj* x_461; obj* x_462; uint8 x_463; obj* x_464; obj* x_465; 
x_460 = lean::cnstr_get(x_416, 1);
lean::inc(x_460);
x_461 = lean::cnstr_get(x_416, 2);
lean::inc(x_461);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_462 = x_416;
} else {
 lean::dec_ref(x_416);
 x_462 = lean::box(0);
}
x_463 = 0;
if (lean::is_scalar(x_462)) {
 x_464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_464 = x_462;
}
lean::cnstr_set(x_464, 0, x_417);
lean::cnstr_set(x_464, 1, x_460);
lean::cnstr_set(x_464, 2, x_461);
lean::cnstr_set(x_464, 3, x_459);
lean::cnstr_set_scalar(x_464, sizeof(void*)*4, x_463);
x_465 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_465, 0, x_464);
lean::cnstr_set(x_465, 1, x_326);
lean::cnstr_set(x_465, 2, x_327);
lean::cnstr_set(x_465, 3, x_328);
lean::cnstr_set_scalar(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8 x_466; 
x_466 = lean::cnstr_get_scalar<uint8>(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; obj* x_478; 
x_467 = lean::cnstr_get(x_416, 1);
lean::inc(x_467);
x_468 = lean::cnstr_get(x_416, 2);
lean::inc(x_468);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_469 = x_416;
} else {
 lean::dec_ref(x_416);
 x_469 = lean::box(0);
}
x_470 = lean::cnstr_get(x_459, 0);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_459, 1);
lean::inc(x_471);
x_472 = lean::cnstr_get(x_459, 2);
lean::inc(x_472);
x_473 = lean::cnstr_get(x_459, 3);
lean::inc(x_473);
if (lean::is_exclusive(x_459)) {
 lean::cnstr_release(x_459, 0);
 lean::cnstr_release(x_459, 1);
 lean::cnstr_release(x_459, 2);
 lean::cnstr_release(x_459, 3);
 x_474 = x_459;
} else {
 lean::dec_ref(x_459);
 x_474 = lean::box(0);
}
lean::inc(x_417);
if (lean::is_scalar(x_474)) {
 x_475 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_475 = x_474;
}
lean::cnstr_set(x_475, 0, x_417);
lean::cnstr_set(x_475, 1, x_467);
lean::cnstr_set(x_475, 2, x_468);
lean::cnstr_set(x_475, 3, x_470);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_476 = x_417;
} else {
 lean::dec_ref(x_417);
 x_476 = lean::box(0);
}
lean::cnstr_set_scalar(x_475, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_476)) {
 x_477 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_477 = x_476;
}
lean::cnstr_set(x_477, 0, x_473);
lean::cnstr_set(x_477, 1, x_326);
lean::cnstr_set(x_477, 2, x_327);
lean::cnstr_set(x_477, 3, x_328);
lean::cnstr_set_scalar(x_477, sizeof(void*)*4, x_445);
if (lean::is_scalar(x_469)) {
 x_478 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_478 = x_469;
}
lean::cnstr_set(x_478, 0, x_475);
lean::cnstr_set(x_478, 1, x_471);
lean::cnstr_set(x_478, 2, x_472);
lean::cnstr_set(x_478, 3, x_477);
lean::cnstr_set_scalar(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; uint8 x_488; obj* x_489; obj* x_490; 
x_479 = lean::cnstr_get(x_416, 1);
lean::inc(x_479);
x_480 = lean::cnstr_get(x_416, 2);
lean::inc(x_480);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 lean::cnstr_release(x_416, 1);
 lean::cnstr_release(x_416, 2);
 lean::cnstr_release(x_416, 3);
 x_481 = x_416;
} else {
 lean::dec_ref(x_416);
 x_481 = lean::box(0);
}
x_482 = lean::cnstr_get(x_417, 0);
lean::inc(x_482);
x_483 = lean::cnstr_get(x_417, 1);
lean::inc(x_483);
x_484 = lean::cnstr_get(x_417, 2);
lean::inc(x_484);
x_485 = lean::cnstr_get(x_417, 3);
lean::inc(x_485);
if (lean::is_exclusive(x_417)) {
 lean::cnstr_release(x_417, 0);
 lean::cnstr_release(x_417, 1);
 lean::cnstr_release(x_417, 2);
 lean::cnstr_release(x_417, 3);
 x_486 = x_417;
} else {
 lean::dec_ref(x_417);
 x_486 = lean::box(0);
}
if (lean::is_scalar(x_486)) {
 x_487 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_487 = x_486;
}
lean::cnstr_set(x_487, 0, x_482);
lean::cnstr_set(x_487, 1, x_483);
lean::cnstr_set(x_487, 2, x_484);
lean::cnstr_set(x_487, 3, x_485);
lean::cnstr_set_scalar(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean::is_scalar(x_481)) {
 x_489 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_489 = x_481;
}
lean::cnstr_set(x_489, 0, x_487);
lean::cnstr_set(x_489, 1, x_479);
lean::cnstr_set(x_489, 2, x_480);
lean::cnstr_set(x_489, 3, x_459);
lean::cnstr_set_scalar(x_489, sizeof(void*)*4, x_488);
x_490 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_490, 0, x_489);
lean::cnstr_set(x_490, 1, x_326);
lean::cnstr_set(x_490, 2, x_327);
lean::cnstr_set(x_490, 3, x_328);
lean::cnstr_set_scalar(x_490, sizeof(void*)*4, x_466);
return x_490;
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
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(obj* x_1, uint32 x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
x_8 = lean::string_utf8_at_end(x_1, x_4);
if (x_8 == 0)
{
uint32 x_9; obj* x_10; obj* x_11; 
x_9 = lean::string_utf8_get(x_1, x_4);
x_10 = lean::string_utf8_next(x_1, x_4);
lean::inc(x_7);
x_11 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_7, x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_10);
lean::dec(x_10);
x_13 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_7, x_9, x_12);
lean::cnstr_set(x_3, 1, x_13);
return x_3;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_15 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_2, x_14, x_10);
lean::dec(x_10);
x_16 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_7, x_9, x_15);
lean::cnstr_set(x_3, 1, x_16);
return x_3;
}
}
else
{
obj* x_17; 
lean::dec(x_6);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_3, 0, x_17);
return x_3;
}
}
else
{
obj* x_18; obj* x_19; uint8 x_20; 
x_18 = lean::cnstr_get(x_3, 0);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_3);
x_20 = lean::string_utf8_at_end(x_1, x_4);
if (x_20 == 0)
{
uint32 x_21; obj* x_22; obj* x_23; 
x_21 = lean::string_utf8_get(x_1, x_4);
x_22 = lean::string_utf8_next(x_1, x_4);
lean::inc(x_19);
x_23 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_19, x_21);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l___private_init_lean_parser_trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_22);
lean::dec(x_22);
x_25 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_19, x_21, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_18);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_23, 0);
lean::inc(x_27);
lean::dec(x_23);
x_28 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_2, x_27, x_22);
lean::dec(x_22);
x_29 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_19, x_21, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_18);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_18);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_2);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_19);
return x_32;
}
}
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_RBNode_find___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__3___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__4___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__6___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_RBNode_ins___main___at___private_init_lean_parser_trie_2__insertAux___main___spec__7___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_5 = l_RBNode_insert___at___private_init_lean_parser_trie_2__insertAux___main___spec__5___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_2__insertAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_2__insertAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_trie_2__insertAux___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Trie_insert___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l___private_init_lean_parser_trie_2__insertAux___main___rarg(x_2, x_3, x_1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_Trie_insert(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_insert___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_Trie_insert___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Trie_insert___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(obj* x_1, uint32 x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint32 x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::unbox_uint32(x_5);
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
lean::dec(x_4);
x_10 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_11 = x_10 < x_2;
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_6);
return x_12;
}
else
{
lean::dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
uint32 x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_7 = lean::string_utf8_get(x_1, x_3);
x_8 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
x_9 = l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(x_5, x_7);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_2 = x_11;
x_3 = x_8;
goto _start;
}
}
else
{
lean::dec(x_5);
lean::dec(x_3);
return x_4;
}
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_RBNode_find___main___at___private_init_lean_parser_trie_3__findAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_3__findAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_3__findAux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_3__findAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_3__findAux___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_Trie_find___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l___private_init_lean_parser_trie_3__findAux___main___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Trie_find(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_find___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_Trie_find___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Trie_find___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_2);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_4__updtAcc___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(obj* x_1, uint32 x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint32 x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::unbox_uint32(x_5);
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32 x_10; uint8 x_11; 
lean::dec(x_4);
x_10 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_11 = x_10 < x_2;
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_6);
return x_12;
}
else
{
lean::dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::string_utf8_at_end(x_1, x_3);
if (x_7 == 0)
{
obj* x_8; uint32 x_9; obj* x_10; obj* x_11; 
lean::inc(x_3);
x_8 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_5, x_3, x_4);
lean::dec(x_4);
x_9 = lean::string_utf8_get(x_1, x_3);
x_10 = lean::string_utf8_next(x_1, x_3);
lean::dec(x_3);
x_11 = l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(x_6, x_9);
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_10);
return x_8;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_2 = x_12;
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
else
{
obj* x_14; 
lean::dec(x_6);
x_14 = l___private_init_lean_parser_trie_4__updtAcc___rarg(x_5, x_3, x_4);
lean::dec(x_4);
return x_14;
}
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_4 = l_RBNode_find___main___at___private_init_lean_parser_trie_5__matchPrefixAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_5__matchPrefixAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_trie_5__matchPrefixAux___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l___private_init_lean_parser_trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Trie_matchPrefix(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_matchPrefix___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Trie_matchPrefix___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
return x_5;
}
else
{
obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = 0;
lean::inc(x_2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1(x_4, x_2);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
}
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint32 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 3);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2___rarg(x_1, x_3);
x_8 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean::string_append(x_10, x_9);
lean::dec(x_9);
x_12 = lean::string_append(x_11, x_10);
x_13 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l___private_init_lean_parser_trie_6__toStringAux___main___rarg(x_5);
x_15 = lean::box(1);
x_16 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1(x_14, x_15);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(2u);
x_18 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::format_group_core(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_13);
lean::cnstr_set(x_21, 1, x_20);
x_1 = x_21;
x_2 = x_6;
goto _start;
}
}
}
obj* l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_6__toStringAux___main___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::box(0);
x_4 = l_RBNode_fold___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__2___rarg(x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_trie_6__toStringAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_6__toStringAux___main___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_trie_6__toStringAux___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_trie_6__toStringAux___main___rarg(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_trie_6__toStringAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_trie_6__toStringAux___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_Trie_HasToString___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l___private_init_lean_parser_trie_6__toStringAux___main___rarg(x_1);
x_3 = lean::box(1);
x_4 = l_Lean_Format_joinSep___main___at___private_init_lean_parser_trie_6__toStringAux___main___spec__1(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_Options_empty;
x_6 = l_Lean_Format_pretty(x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_Trie_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Trie_HasToString___rarg), 1, 0);
return x_2;
}
}
obj* initialize_init_data_rbmap_default(obj*);
obj* initialize_init_lean_format(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_trie(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_Trie_empty___closed__1 = _init_l_Lean_Parser_Trie_empty___closed__1();
lean::mark_persistent(l_Lean_Parser_Trie_empty___closed__1);
l_Lean_Parser_Trie_HasEmptyc___closed__1 = _init_l_Lean_Parser_Trie_HasEmptyc___closed__1();
lean::mark_persistent(l_Lean_Parser_Trie_HasEmptyc___closed__1);
return w;
}

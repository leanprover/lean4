// Lean compiler output
// Module: init.lean.parser.syntax
// Imports: init.lean.name init.lean.parser.parsec
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
obj* l_Lean_Parser_Syntax_format___main___closed__7;
obj* l_Lean_Parser_Syntax_replace(obj*, obj*);
obj* l_Lean_Parser_Syntax_format___main___closed__3;
uint8 l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2(obj*, uint8, obj*);
obj* l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(obj*, obj*, obj*);
obj* l_Lean_Parser_macroScopes_flip___main___boxed(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_Syntax_flipScopes___main(obj*, obj*);
obj* l_Lean_Parser_macroScopes_flip___main(obj*, obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Parser_Syntax_getHeadInfo___boxed(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6___boxed(obj*, obj*);
extern obj* l_Lean_Format_paren___closed__2;
obj* l_List_map___main___at_Lean_Parser_Syntax_asNode___main___spec__1(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1(obj*, obj*);
obj* l_Lean_Parser_Syntax_updateLeading___closed__1;
obj* l_Lean_Parser_Syntax_Lean_HasFormat;
obj* l_Lean_Parser_MacroScope_DecidableEq;
obj* l_Lean_Format_group___main(obj*);
obj* l_Lean_Parser_Syntax_isOfKind___boxed(obj*, obj*);
obj* l_Lean_Parser_Syntax_isOfKind___main___boxed(obj*, obj*);
obj* l_Lean_Parser_choice;
obj* l_Lean_Parser_Syntax_format___main___closed__5;
obj* l_Lean_Parser_Syntax_kind___boxed(obj*);
obj* l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__5(obj*);
obj* l_Lean_Parser_Substring_HasToString;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_fmt___at_Lean_Parser_Syntax_HasToString___spec__1(obj*);
obj* l_Lean_Parser_MacroScope_Lean_HasFormat;
obj* l_List_reverse___rarg(obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_format___main___closed__4;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__1(obj*);
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_Parser_Syntax_format___main___closed__8;
obj* l_Lean_Parser_Syntax_getHeadInfo___main(obj*);
obj* l___private_init_lean_parser_syntax_1__updateLeadingAux___main(obj*, obj*);
obj* l_Lean_Parser_Substring_toString(obj*);
obj* l_Lean_Parser_Syntax_mreplace___main(obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_String_OldIterator_nextn___main(obj*, obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Nat_repr(obj*);
obj* l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_mreplace(obj*);
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_Parser_Syntax_getHeadInfo___main___boxed(obj*);
obj* l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(obj*, obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__8(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(obj*, obj*);
obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_Syntax_mreplace___main___boxed(obj*);
obj* l_Lean_Parser_Syntax_list(obj*);
obj* l_Lean_Parser_Syntax_mreplace___boxed(obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__3(obj*);
obj* l_Lean_Parser_Syntax_kind(obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__4(obj*);
obj* l_Lean_Parser_Syntax_getPos(obj*);
obj* l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(obj*);
obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_Syntax_reprintAtom___main(obj*);
obj* l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1___boxed(obj*, obj*);
obj* l_List_append___rarg(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_String_OldIterator_toEnd___main(obj*);
obj* l_Lean_natHasFormat(obj*);
extern obj* l_Lean_Format_paren___closed__3;
obj* l_Lean_Parser_Syntax_getPos___boxed(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_Syntax_reprint___main___closed__1;
obj* l_Lean_Parser_Syntax_reprintAtom(obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_updateLeading___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_reprint(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_HasRepr___lambda__1(obj*);
obj* l_Lean_Parser_Syntax_updateLeading(obj*, obj*);
obj* l_Lean_Parser_Syntax_kind___main___boxed(obj*);
obj* l___private_init_lean_parser_syntax_1__updateLeadingAux(obj*, obj*);
obj* l_Lean_Parser_Syntax_format___main___closed__6;
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__3;
extern obj* l_Lean_formatKVMap___closed__1;
obj* l_Lean_Parser_Syntax_format___main(obj*);
obj* l_Lean_Parser_Syntax_HasToString;
obj* l_Lean_Parser_Syntax_reprintAtom___boxed(obj*);
obj* l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Substring_toString___boxed(obj*);
obj* l_Lean_Parser_Syntax_getHeadInfo(obj*);
obj* l_Lean_Parser_Inhabited;
obj* l_Lean_Parser_macroScopes_flip(obj*, obj*);
obj* l_Lean_Parser_Syntax_format___main___closed__1;
obj* l_Lean_Parser_Syntax_reprintAtom___main___boxed(obj*);
obj* l_Lean_Parser_Syntax_asNode(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Parser_Syntax_flipScopes(obj*, obj*);
extern obj* l_List_mmap___main___rarg___closed__1;
obj* l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(obj*);
obj* l_Lean_Parser_Syntax_kind___main(obj*);
obj* l_Lean_Parser_macroScopes_flip___boxed(obj*, obj*);
obj* l_String_OldIterator_extract___main(obj*, obj*);
obj* l_Lean_Parser_Syntax_reprint___main(obj*);
obj* l_List_foldl___main___at_String_join___spec__1(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_Syntax_format(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
uint8 l_Lean_Parser_Syntax_isOfKind(obj*, obj*);
obj* l_Lean_Parser_Syntax_format___main___closed__2;
obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
extern obj* l_String_splitAux___main___closed__1;
obj* l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___boxed(obj*);
obj* l_Lean_Parser_Syntax_mreplace___rarg(obj*, obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* _init_l_Lean_Parser_choice() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("choice");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_noKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("noKind");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_MacroScope_DecidableEq() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_MacroScope_Lean_HasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_natHasFormat), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_Inhabited() {
_start:
{
obj* x_1; 
x_1 = lean::box(3);
return x_1;
}
}
obj* l_Lean_Parser_Substring_toString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_String_OldIterator_extract___main(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Substring_toString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Substring_toString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Substring_ofString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_2);
lean::inc(x_3);
x_4 = l_String_OldIterator_toEnd___main(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Substring_HasToString() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Substring_toString___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_macroScopes_flip___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
lean::inc(x_1);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_Lean_Parser_macroScopes_flip___main(x_1, x_5);
if (lean::obj_tag(x_6) == 0)
{
lean::cnstr_set(x_2, 1, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::nat_dec_eq(x_4, x_7);
lean::dec(x_7);
if (x_9 == 0)
{
lean::dec(x_8);
lean::cnstr_set(x_2, 1, x_6);
return x_2;
}
else
{
lean::dec(x_6);
lean::free_heap_obj(x_2);
lean::dec(x_4);
return x_8;
}
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
x_12 = l_Lean_Parser_macroScopes_flip___main(x_1, x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; 
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
x_16 = lean::nat_dec_eq(x_10, x_14);
lean::dec(x_14);
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
else
{
lean::dec(x_12);
lean::dec(x_10);
return x_15;
}
}
}
}
}
}
obj* l_Lean_Parser_macroScopes_flip___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_macroScopes_flip___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_macroScopes_flip(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_macroScopes_flip___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_macroScopes_flip___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_macroScopes_flip(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Syntax_flipScopes___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
lean::dec(x_1);
return x_2;
}
case 1:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 4);
x_7 = l_Lean_Parser_macroScopes_flip___main(x_6, x_1);
lean::dec(x_6);
lean::cnstr_set(x_4, 4, x_7);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_4, 1);
x_10 = lean::cnstr_get(x_4, 2);
x_11 = lean::cnstr_get(x_4, 3);
x_12 = lean::cnstr_get(x_4, 4);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_4);
x_13 = l_Lean_Parser_macroScopes_flip___main(x_12, x_1);
lean::dec(x_12);
x_14 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_10);
lean::cnstr_set(x_14, 3, x_11);
lean::cnstr_set(x_14, 4, x_13);
lean::cnstr_set(x_2, 0, x_14);
return x_2;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_15, 1);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_15, 2);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_15, 3);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_15, 4);
lean::inc(x_20);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 lean::cnstr_release(x_15, 3);
 lean::cnstr_release(x_15, 4);
 x_21 = x_15;
} else {
 lean::dec_ref(x_15);
 x_21 = lean::box(0);
}
x_22 = l_Lean_Parser_macroScopes_flip___main(x_20, x_1);
lean::dec(x_20);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_17);
lean::cnstr_set(x_23, 2, x_18);
lean::cnstr_set(x_23, 3, x_19);
lean::cnstr_set(x_23, 4, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
case 2:
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_2);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = lean::cnstr_get(x_2, 0);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_26, 2);
x_29 = l_Lean_Parser_macroScopes_flip___main(x_28, x_1);
lean::dec(x_28);
lean::cnstr_set(x_26, 2, x_29);
return x_2;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_26, 0);
x_31 = lean::cnstr_get(x_26, 1);
x_32 = lean::cnstr_get(x_26, 2);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::dec(x_26);
x_33 = l_Lean_Parser_macroScopes_flip___main(x_32, x_1);
lean::dec(x_32);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set(x_34, 1, x_31);
lean::cnstr_set(x_34, 2, x_33);
lean::cnstr_set(x_2, 0, x_34);
return x_2;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_2, 0);
lean::inc(x_35);
lean::dec(x_2);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 lean::cnstr_release(x_35, 1);
 lean::cnstr_release(x_35, 2);
 x_39 = x_35;
} else {
 lean::dec_ref(x_35);
 x_39 = lean::box(0);
}
x_40 = l_Lean_Parser_macroScopes_flip___main(x_38, x_1);
lean::dec(x_38);
if (lean::is_scalar(x_39)) {
 x_41 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_41 = x_39;
}
lean::cnstr_set(x_41, 0, x_36);
lean::cnstr_set(x_41, 1, x_37);
lean::cnstr_set(x_41, 2, x_40);
x_42 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
default: 
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Lean_Parser_Syntax_flipScopes(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Syntax_flipScopes___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Syntax_mkNode(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_List_map___main___at_Lean_Parser_Syntax_asNode___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
x_8 = l_Lean_Parser_Syntax_flipScopes___main(x_7, x_5);
x_9 = l_List_map___main___at_Lean_Parser_Syntax_asNode___main___spec__1(x_1, x_6);
lean::cnstr_set(x_2, 1, x_9);
lean::cnstr_set(x_2, 0, x_8);
return x_2;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_1, 2);
lean::inc(x_12);
x_13 = l_Lean_Parser_Syntax_flipScopes___main(x_12, x_10);
x_14 = l_List_map___main___at_Lean_Parser_Syntax_asNode___main___spec__1(x_1, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_Lean_Parser_Syntax_asNode___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 2)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::inc(x_2);
x_5 = l_List_map___main___at_Lean_Parser_Syntax_asNode___main___spec__1(x_2, x_4);
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_2, 2);
lean::dec(x_7);
x_8 = lean::cnstr_get(x_2, 1);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_2, 0);
lean::dec(x_9);
x_10 = lean::box(0);
lean::cnstr_set(x_2, 2, x_10);
lean::cnstr_set(x_2, 1, x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_2);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_5);
lean::cnstr_set(x_13, 2, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_1);
x_15 = lean::box(0);
return x_15;
}
}
}
obj* l_Lean_Parser_Syntax_asNode(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_list(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_noKind;
x_3 = l_Lean_Parser_Syntax_mkNode(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Parser_Syntax_kind___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 2)
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
}
obj* l_Lean_Parser_Syntax_kind___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_kind___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_kind(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_kind___main(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_kind___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_kind(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 2)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean_name_dec_eq(x_1, x_4);
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
obj* l_Lean_Parser_Syntax_isOfKind___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Parser_Syntax_isOfKind___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_Parser_Syntax_isOfKind(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Parser_Syntax_isOfKind___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_Syntax_isOfKind___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Parser_Syntax_isOfKind(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
lean::dec(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
lean::inc(x_2);
lean::inc(x_1);
x_14 = l_Lean_Parser_Syntax_mreplace___main___rarg(x_1, x_2, x_9);
x_15 = l_List_mmap___main___rarg___closed__1;
x_16 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_14);
x_17 = l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___rarg(x_1, x_2, x_10);
x_18 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_16, x_17);
return x_18;
}
}
}
obj* l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::apply_2(x_5, lean::box(0), x_2);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::apply_2(x_8, lean::box(0), x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::apply_2(x_5, lean::box(0), x_7);
return x_8;
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
lean::dec(x_2);
x_10 = l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___rarg(x_1, x_3, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__2), 4, 3);
lean::closure_set(x_11, 0, x_6);
lean::closure_set(x_11, 1, x_7);
lean::closure_set(x_11, 2, x_9);
x_12 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::apply_2(x_15, lean::box(0), x_13);
return x_16;
}
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 2)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_2);
x_12 = lean::apply_1(x_2, x_3);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__3), 5, 4);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_10);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_11);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
else
{
obj* x_15; 
x_15 = lean::box(0);
x_4 = x_15;
goto block_9;
}
block_9:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::inc(x_3);
x_6 = lean::apply_1(x_2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Syntax_mreplace___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_6, x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_Syntax_mreplace___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Syntax_mreplace___main___rarg), 3, 0);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mmap___main___at_Lean_Parser_Syntax_mreplace___main___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_mreplace___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_mreplace___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_Syntax_mreplace___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_Syntax_mreplace(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Syntax_mreplace___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_mreplace___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_mreplace(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_7 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_1, x_5);
x_8 = l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(x_1, x_6);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_11 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_1, x_9);
x_12 = l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(x_1, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_2) == 2)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::inc(x_1);
lean::inc(x_2);
x_8 = lean::apply_1(x_1, x_2);
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_2, 0);
lean::dec(x_10);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_11; 
lean::dec(x_8);
x_11 = !lean::is_exclusive(x_7);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_7, 1);
x_13 = l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(x_1, x_12);
lean::cnstr_set(x_7, 1, x_13);
return x_2;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_7, 0);
x_15 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_7);
x_17 = l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(x_1, x_15);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_16);
lean::cnstr_set(x_2, 0, x_18);
return x_2;
}
}
else
{
obj* x_19; 
lean::free_heap_obj(x_2);
lean::dec(x_7);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
return x_19;
}
}
else
{
lean::dec(x_2);
if (lean::obj_tag(x_8) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_8);
x_20 = lean::cnstr_get(x_7, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_7, 1);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_7, 2);
lean::inc(x_22);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_23 = x_7;
} else {
 lean::dec_ref(x_7);
 x_23 = lean::box(0);
}
x_24 = l_List_mmap___main___at_Lean_Parser_Syntax_replace___spec__2(x_1, x_21);
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_22);
x_26 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_27; 
lean::dec(x_7);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_8, 0);
lean::inc(x_27);
lean::dec(x_8);
return x_27;
}
}
}
else
{
obj* x_28; 
x_28 = lean::box(0);
x_3 = x_28;
goto block_6;
}
block_6:
{
obj* x_4; 
lean::dec(x_3);
lean::inc(x_2);
x_4 = lean::apply_1(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_4);
return x_2;
}
else
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
}
}
obj* l_Lean_Parser_Syntax_replace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_replace___spec__1(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_syntax_1__updateLeadingAux___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_5);
lean::free_heap_obj(x_1);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_5, 0);
x_10 = lean::cnstr_get(x_9, 2);
lean::inc(x_10);
x_11 = !lean::is_exclusive(x_4);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::cnstr_get(x_4, 0);
lean::dec(x_12);
x_13 = !lean::is_exclusive(x_9);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_9, 1);
x_15 = lean::cnstr_get(x_9, 2);
lean::dec(x_15);
x_16 = lean::cnstr_get(x_9, 0);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
x_19 = lean::nat_sub(x_14, x_18);
lean::dec(x_18);
lean::inc(x_2);
x_20 = l_String_OldIterator_nextn___main(x_2, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_9, 0, x_21);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_1);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_17);
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_9, 1);
lean::inc(x_24);
lean::dec(x_9);
x_25 = lean::cnstr_get(x_10, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_2, 1);
lean::inc(x_26);
x_27 = lean::nat_sub(x_24, x_26);
lean::dec(x_26);
lean::inc(x_2);
x_28 = l_String_OldIterator_nextn___main(x_2, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_2);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_24);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_5, 0, x_30);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_1);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_33 = lean::cnstr_get(x_4, 1);
lean::inc(x_33);
lean::dec(x_4);
x_34 = lean::cnstr_get(x_9, 1);
lean::inc(x_34);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_35 = x_9;
} else {
 lean::dec_ref(x_9);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_10, 1);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_2, 1);
lean::inc(x_37);
x_38 = lean::nat_sub(x_34, x_37);
lean::dec(x_37);
lean::inc(x_2);
x_39 = l_String_OldIterator_nextn___main(x_2, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_2);
lean::cnstr_set(x_40, 1, x_39);
if (lean::is_scalar(x_35)) {
 x_41 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_41 = x_35;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_34);
lean::cnstr_set(x_41, 2, x_10);
lean::cnstr_set(x_5, 0, x_41);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_33);
lean::cnstr_set(x_1, 0, x_42);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_1);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_36);
return x_44;
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_45 = lean::cnstr_get(x_5, 0);
lean::inc(x_45);
lean::dec(x_5);
x_46 = lean::cnstr_get(x_45, 2);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_4, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_48 = x_4;
} else {
 lean::dec_ref(x_4);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_45, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 lean::cnstr_release(x_45, 2);
 x_50 = x_45;
} else {
 lean::dec_ref(x_45);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_46, 1);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_2, 1);
lean::inc(x_52);
x_53 = lean::nat_sub(x_49, x_52);
lean::dec(x_52);
lean::inc(x_2);
x_54 = l_String_OldIterator_nextn___main(x_2, x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_2);
lean::cnstr_set(x_55, 1, x_54);
if (lean::is_scalar(x_50)) {
 x_56 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_56 = x_50;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_49);
lean::cnstr_set(x_56, 2, x_46);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
if (lean::is_scalar(x_48)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_48;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_47);
lean::cnstr_set(x_1, 0, x_58);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_1);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
return x_60;
}
}
}
else
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_1, 0);
lean::inc(x_61);
lean::dec(x_1);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_62);
lean::dec(x_61);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_2);
return x_64;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_65 = lean::cnstr_get(x_62, 0);
lean::inc(x_65);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_66 = x_62;
} else {
 lean::dec_ref(x_62);
 x_66 = lean::box(0);
}
x_67 = lean::cnstr_get(x_65, 2);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_61, 1);
lean::inc(x_68);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_69 = x_61;
} else {
 lean::dec_ref(x_61);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_65, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_65)) {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 lean::cnstr_release(x_65, 2);
 x_71 = x_65;
} else {
 lean::dec_ref(x_65);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_67, 1);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_2, 1);
lean::inc(x_73);
x_74 = lean::nat_sub(x_70, x_73);
lean::dec(x_73);
lean::inc(x_2);
x_75 = l_String_OldIterator_nextn___main(x_2, x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_2);
lean::cnstr_set(x_76, 1, x_75);
if (lean::is_scalar(x_71)) {
 x_77 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_77 = x_71;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_70);
lean::cnstr_set(x_77, 2, x_67);
if (lean::is_scalar(x_66)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_66;
}
lean::cnstr_set(x_78, 0, x_77);
if (lean::is_scalar(x_69)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_69;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_68);
x_80 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_72);
return x_82;
}
}
}
case 1:
{
uint8 x_83; 
x_83 = !lean::is_exclusive(x_1);
if (x_83 == 0)
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_1, 0);
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_87; 
lean::dec(x_85);
lean::free_heap_obj(x_1);
lean::dec(x_84);
x_86 = lean::box(0);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_2);
return x_87;
}
else
{
uint8 x_88; 
x_88 = !lean::is_exclusive(x_85);
if (x_88 == 0)
{
obj* x_89; obj* x_90; uint8 x_91; 
x_89 = lean::cnstr_get(x_85, 0);
x_90 = lean::cnstr_get(x_89, 2);
lean::inc(x_90);
x_91 = !lean::is_exclusive(x_84);
if (x_91 == 0)
{
obj* x_92; uint8 x_93; 
x_92 = lean::cnstr_get(x_84, 0);
lean::dec(x_92);
x_93 = !lean::is_exclusive(x_89);
if (x_93 == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_94 = lean::cnstr_get(x_89, 1);
x_95 = lean::cnstr_get(x_89, 2);
lean::dec(x_95);
x_96 = lean::cnstr_get(x_89, 0);
lean::dec(x_96);
x_97 = lean::cnstr_get(x_90, 1);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_2, 1);
lean::inc(x_98);
x_99 = lean::nat_sub(x_94, x_98);
lean::dec(x_98);
lean::inc(x_2);
x_100 = l_String_OldIterator_nextn___main(x_2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_2);
lean::cnstr_set(x_101, 1, x_100);
lean::cnstr_set(x_89, 0, x_101);
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_1);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_97);
return x_103;
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_104 = lean::cnstr_get(x_89, 1);
lean::inc(x_104);
lean::dec(x_89);
x_105 = lean::cnstr_get(x_90, 1);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_2, 1);
lean::inc(x_106);
x_107 = lean::nat_sub(x_104, x_106);
lean::dec(x_106);
lean::inc(x_2);
x_108 = l_String_OldIterator_nextn___main(x_2, x_107);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_2);
lean::cnstr_set(x_109, 1, x_108);
x_110 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_104);
lean::cnstr_set(x_110, 2, x_90);
lean::cnstr_set(x_85, 0, x_110);
x_111 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_111, 0, x_1);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_105);
return x_112;
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_113 = lean::cnstr_get(x_84, 1);
x_114 = lean::cnstr_get(x_84, 2);
x_115 = lean::cnstr_get(x_84, 3);
x_116 = lean::cnstr_get(x_84, 4);
lean::inc(x_116);
lean::inc(x_115);
lean::inc(x_114);
lean::inc(x_113);
lean::dec(x_84);
x_117 = lean::cnstr_get(x_89, 1);
lean::inc(x_117);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 lean::cnstr_release(x_89, 2);
 x_118 = x_89;
} else {
 lean::dec_ref(x_89);
 x_118 = lean::box(0);
}
x_119 = lean::cnstr_get(x_90, 1);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_2, 1);
lean::inc(x_120);
x_121 = lean::nat_sub(x_117, x_120);
lean::dec(x_120);
lean::inc(x_2);
x_122 = l_String_OldIterator_nextn___main(x_2, x_121);
x_123 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_123, 0, x_2);
lean::cnstr_set(x_123, 1, x_122);
if (lean::is_scalar(x_118)) {
 x_124 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_124 = x_118;
}
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_117);
lean::cnstr_set(x_124, 2, x_90);
lean::cnstr_set(x_85, 0, x_124);
x_125 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_125, 0, x_85);
lean::cnstr_set(x_125, 1, x_113);
lean::cnstr_set(x_125, 2, x_114);
lean::cnstr_set(x_125, 3, x_115);
lean::cnstr_set(x_125, 4, x_116);
lean::cnstr_set(x_1, 0, x_125);
x_126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_126, 0, x_1);
x_127 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_119);
return x_127;
}
}
else
{
obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_128 = lean::cnstr_get(x_85, 0);
lean::inc(x_128);
lean::dec(x_85);
x_129 = lean::cnstr_get(x_128, 2);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_84, 1);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_84, 2);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_84, 3);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_84, 4);
lean::inc(x_133);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 lean::cnstr_release(x_84, 2);
 lean::cnstr_release(x_84, 3);
 lean::cnstr_release(x_84, 4);
 x_134 = x_84;
} else {
 lean::dec_ref(x_84);
 x_134 = lean::box(0);
}
x_135 = lean::cnstr_get(x_128, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_128)) {
 lean::cnstr_release(x_128, 0);
 lean::cnstr_release(x_128, 1);
 lean::cnstr_release(x_128, 2);
 x_136 = x_128;
} else {
 lean::dec_ref(x_128);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_129, 1);
lean::inc(x_137);
x_138 = lean::cnstr_get(x_2, 1);
lean::inc(x_138);
x_139 = lean::nat_sub(x_135, x_138);
lean::dec(x_138);
lean::inc(x_2);
x_140 = l_String_OldIterator_nextn___main(x_2, x_139);
x_141 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_141, 0, x_2);
lean::cnstr_set(x_141, 1, x_140);
if (lean::is_scalar(x_136)) {
 x_142 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_142 = x_136;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_135);
lean::cnstr_set(x_142, 2, x_129);
x_143 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_143, 0, x_142);
if (lean::is_scalar(x_134)) {
 x_144 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_144 = x_134;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_130);
lean::cnstr_set(x_144, 2, x_131);
lean::cnstr_set(x_144, 3, x_132);
lean::cnstr_set(x_144, 4, x_133);
lean::cnstr_set(x_1, 0, x_144);
x_145 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_145, 0, x_1);
x_146 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_137);
return x_146;
}
}
}
else
{
obj* x_147; obj* x_148; 
x_147 = lean::cnstr_get(x_1, 0);
lean::inc(x_147);
lean::dec(x_1);
x_148 = lean::cnstr_get(x_147, 0);
lean::inc(x_148);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_150; 
lean::dec(x_148);
lean::dec(x_147);
x_149 = lean::box(0);
x_150 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_2);
return x_150;
}
else
{
obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_151 = lean::cnstr_get(x_148, 0);
lean::inc(x_151);
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 x_152 = x_148;
} else {
 lean::dec_ref(x_148);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_151, 2);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_147, 1);
lean::inc(x_154);
x_155 = lean::cnstr_get(x_147, 2);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_147, 3);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_147, 4);
lean::inc(x_157);
if (lean::is_exclusive(x_147)) {
 lean::cnstr_release(x_147, 0);
 lean::cnstr_release(x_147, 1);
 lean::cnstr_release(x_147, 2);
 lean::cnstr_release(x_147, 3);
 lean::cnstr_release(x_147, 4);
 x_158 = x_147;
} else {
 lean::dec_ref(x_147);
 x_158 = lean::box(0);
}
x_159 = lean::cnstr_get(x_151, 1);
lean::inc(x_159);
if (lean::is_exclusive(x_151)) {
 lean::cnstr_release(x_151, 0);
 lean::cnstr_release(x_151, 1);
 lean::cnstr_release(x_151, 2);
 x_160 = x_151;
} else {
 lean::dec_ref(x_151);
 x_160 = lean::box(0);
}
x_161 = lean::cnstr_get(x_153, 1);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_2, 1);
lean::inc(x_162);
x_163 = lean::nat_sub(x_159, x_162);
lean::dec(x_162);
lean::inc(x_2);
x_164 = l_String_OldIterator_nextn___main(x_2, x_163);
x_165 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_165, 0, x_2);
lean::cnstr_set(x_165, 1, x_164);
if (lean::is_scalar(x_160)) {
 x_166 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_166 = x_160;
}
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_159);
lean::cnstr_set(x_166, 2, x_153);
if (lean::is_scalar(x_152)) {
 x_167 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_167 = x_152;
}
lean::cnstr_set(x_167, 0, x_166);
if (lean::is_scalar(x_158)) {
 x_168 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_168 = x_158;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_154);
lean::cnstr_set(x_168, 2, x_155);
lean::cnstr_set(x_168, 3, x_156);
lean::cnstr_set(x_168, 4, x_157);
x_169 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_169, 0, x_168);
x_170 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_170, 0, x_169);
x_171 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_161);
return x_171;
}
}
}
default: 
{
obj* x_172; obj* x_173; 
lean::dec(x_1);
x_172 = lean::box(0);
x_173 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_2);
return x_173;
}
}
}
}
obj* l___private_init_lean_parser_syntax_1__updateLeadingAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_syntax_1__updateLeadingAux___main(x_1, x_2);
return x_3;
}
}
obj* l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_9 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_updateLeading___spec__1(x_1, x_7, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(x_1, x_8, x_11);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; 
x_14 = lean::cnstr_get(x_12, 0);
lean::cnstr_set(x_2, 1, x_14);
lean::cnstr_set(x_2, 0, x_10);
lean::cnstr_set(x_12, 0, x_2);
return x_12;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_12);
lean::cnstr_set(x_2, 1, x_15);
lean::cnstr_set(x_2, 0, x_10);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_18 = lean::cnstr_get(x_2, 0);
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_2);
lean::inc(x_1);
x_20 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_updateLeading___spec__1(x_1, x_18, x_3);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
lean::dec(x_20);
x_23 = l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(x_1, x_19, x_22);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 x_26 = x_23;
} else {
 lean::dec_ref(x_23);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_24);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
}
}
obj* l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_updateLeading___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
if (lean::obj_tag(x_2) == 2)
{
obj* x_18; obj* x_19; uint8 x_20; 
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::inc(x_1);
lean::inc(x_2);
x_19 = lean::apply_2(x_1, x_2, x_3);
x_20 = !lean::is_exclusive(x_2);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_2, 0);
lean::dec(x_21);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; uint8 x_24; 
lean::dec(x_22);
x_23 = lean::cnstr_get(x_19, 1);
lean::inc(x_23);
lean::dec(x_19);
x_24 = !lean::is_exclusive(x_18);
if (x_24 == 0)
{
obj* x_25; obj* x_26; uint8 x_27; 
x_25 = lean::cnstr_get(x_18, 1);
x_26 = l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(x_1, x_25, x_23);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; 
x_28 = lean::cnstr_get(x_26, 0);
lean::cnstr_set(x_18, 1, x_28);
lean::cnstr_set(x_26, 0, x_2);
return x_26;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_26, 0);
x_30 = lean::cnstr_get(x_26, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_26);
lean::cnstr_set(x_18, 1, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_2);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_18, 0);
x_33 = lean::cnstr_get(x_18, 1);
x_34 = lean::cnstr_get(x_18, 2);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_18);
x_35 = l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(x_1, x_33, x_23);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 lean::cnstr_release(x_35, 1);
 x_38 = x_35;
} else {
 lean::dec_ref(x_35);
 x_38 = lean::box(0);
}
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_32);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_34);
lean::cnstr_set(x_2, 0, x_39);
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_2);
lean::cnstr_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8 x_41; 
lean::free_heap_obj(x_2);
lean::dec(x_18);
lean::dec(x_1);
x_41 = !lean::is_exclusive(x_19);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_19, 0);
lean::dec(x_42);
x_43 = lean::cnstr_get(x_22, 0);
lean::inc(x_43);
lean::dec(x_22);
lean::cnstr_set(x_19, 0, x_43);
return x_19;
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = lean::cnstr_get(x_19, 1);
lean::inc(x_44);
lean::dec(x_19);
x_45 = lean::cnstr_get(x_22, 0);
lean::inc(x_45);
lean::dec(x_22);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
obj* x_47; 
lean::dec(x_2);
x_47 = lean::cnstr_get(x_19, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_47);
x_48 = lean::cnstr_get(x_19, 1);
lean::inc(x_48);
lean::dec(x_19);
x_49 = lean::cnstr_get(x_18, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_18, 1);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_18, 2);
lean::inc(x_51);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 x_52 = x_18;
} else {
 lean::dec_ref(x_18);
 x_52 = lean::box(0);
}
x_53 = l_List_mmap___main___at_Lean_Parser_Syntax_updateLeading___spec__2(x_1, x_50, x_48);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 x_56 = x_53;
} else {
 lean::dec_ref(x_53);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_52;
}
lean::cnstr_set(x_57, 0, x_49);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_51);
x_58 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
if (lean::is_scalar(x_56)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_56;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_18);
lean::dec(x_1);
x_60 = lean::cnstr_get(x_19, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 x_61 = x_19;
} else {
 lean::dec_ref(x_19);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_47, 0);
lean::inc(x_62);
lean::dec(x_47);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_60);
return x_63;
}
}
}
else
{
obj* x_64; 
x_64 = lean::box(0);
x_4 = x_64;
goto block_17;
}
block_17:
{
obj* x_5; obj* x_6; 
lean::dec(x_4);
lean::inc(x_2);
x_5 = lean::apply_2(x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
lean::dec(x_6);
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
lean::cnstr_set(x_5, 0, x_2);
return x_5;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8 x_11; 
lean::dec(x_2);
x_11 = !lean::is_exclusive(x_5);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_5, 0);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
lean::cnstr_set(x_5, 0, x_13);
return x_5;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_5, 1);
lean::inc(x_14);
lean::dec(x_5);
x_15 = lean::cnstr_get(x_6, 0);
lean::inc(x_15);
lean::dec(x_6);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
}
}
}
}
obj* _init_l_Lean_Parser_Syntax_updateLeading___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_syntax_1__updateLeadingAux), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_Syntax_updateLeading(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_3);
x_5 = l_Lean_Parser_Syntax_updateLeading___closed__1;
x_6 = l_Lean_Parser_Syntax_mreplace___main___at_Lean_Parser_Syntax_updateLeading___spec__1(x_5, x_2, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
}
obj* l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1(x_1, x_4);
x_6 = l_Lean_Parser_Syntax_getHeadInfo___main(x_3);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
return x_5;
}
else
{
lean::dec(x_5);
return x_6;
}
}
}
}
obj* l_Lean_Parser_Syntax_getHeadInfo___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
return x_3;
}
case 1:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
return x_5;
}
case 2:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::box(0);
x_8 = lean::cnstr_get(x_6, 1);
x_9 = l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1(x_7, x_8);
return x_9;
}
default: 
{
obj* x_10; 
x_10 = lean::box(0);
return x_10;
}
}
}
}
obj* l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldr___main___at_Lean_Parser_Syntax_getHeadInfo___main___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Syntax_getHeadInfo___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_getHeadInfo___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_getHeadInfo(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_getHeadInfo___main(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_getHeadInfo___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_getHeadInfo(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_getPos(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_getHeadInfo___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_Lean_Parser_Syntax_getPos___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_getPos(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_reprintAtom___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 0);
x_7 = l_Lean_Parser_Substring_toString(x_6);
x_8 = lean::string_append(x_7, x_4);
x_9 = lean::cnstr_get(x_5, 2);
x_10 = l_Lean_Parser_Substring_toString(x_9);
x_11 = lean::string_append(x_8, x_10);
lean::dec(x_10);
return x_11;
}
}
}
obj* l_Lean_Parser_Syntax_reprintAtom___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_reprintAtom___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_reprintAtom(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_reprintAtom___main(x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_reprintAtom___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_reprintAtom(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_Parser_Syntax_reprint___main(x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
lean::dec(x_6);
lean::free_heap_obj(x_1);
lean::dec(x_5);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
lean::dec(x_6);
x_9 = l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1(x_5);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
lean::dec(x_9);
lean::dec(x_8);
lean::free_heap_obj(x_1);
x_10 = lean::box(0);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_9);
if (x_11 == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_9, 0);
lean::cnstr_set(x_1, 1, x_12);
lean::cnstr_set(x_1, 0, x_8);
lean::cnstr_set(x_9, 0, x_1);
return x_9;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
lean::cnstr_set(x_1, 1, x_13);
lean::cnstr_set(x_1, 0, x_8);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_1);
return x_14;
}
}
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_17 = l_Lean_Parser_Syntax_reprint___main(x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
lean::dec(x_17);
lean::dec(x_16);
x_18 = lean::box(0);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_20 = l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1(x_16);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
lean::dec(x_20);
lean::dec(x_19);
x_21 = lean::box(0);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_23 = x_20;
} else {
 lean::dec_ref(x_20);
 x_23 = lean::box(0);
}
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_22);
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
}
uint8 l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
return x_2;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2(x_1, x_2, x_5);
x_7 = lean::string_dec_eq(x_4, x_1);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
return x_6;
}
}
}
}
obj* _init_l_Lean_Parser_Syntax_reprint___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("");
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_reprint___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = !lean::is_exclusive(x_3);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_10 = l_Lean_Parser_Substring_toString(x_9);
lean::dec(x_9);
x_11 = lean::string_append(x_10, x_6);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_8, 2);
lean::inc(x_12);
lean::dec(x_8);
x_13 = l_Lean_Parser_Substring_toString(x_12);
lean::dec(x_12);
x_14 = lean::string_append(x_11, x_13);
lean::dec(x_13);
lean::cnstr_set(x_3, 0, x_14);
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = l_Lean_Parser_Substring_toString(x_16);
lean::dec(x_16);
x_18 = lean::string_append(x_17, x_6);
lean::dec(x_6);
x_19 = lean::cnstr_get(x_15, 2);
lean::inc(x_19);
lean::dec(x_15);
x_20 = l_Lean_Parser_Substring_toString(x_19);
lean::dec(x_19);
x_21 = lean::string_append(x_18, x_20);
lean::dec(x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
}
case 1:
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_24);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_26 = l_Lean_Parser_Substring_toString(x_25);
lean::dec(x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_28; uint8 x_29; 
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_29 = !lean::is_exclusive(x_24);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_24, 0);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = l_Lean_Parser_Substring_toString(x_31);
lean::dec(x_31);
x_33 = l_Lean_Parser_Substring_toString(x_28);
lean::dec(x_28);
x_34 = lean::string_append(x_32, x_33);
lean::dec(x_33);
x_35 = lean::cnstr_get(x_30, 2);
lean::inc(x_35);
lean::dec(x_30);
x_36 = l_Lean_Parser_Substring_toString(x_35);
lean::dec(x_35);
x_37 = lean::string_append(x_34, x_36);
lean::dec(x_36);
lean::cnstr_set(x_24, 0, x_37);
return x_24;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_38 = lean::cnstr_get(x_24, 0);
lean::inc(x_38);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = l_Lean_Parser_Substring_toString(x_39);
lean::dec(x_39);
x_41 = l_Lean_Parser_Substring_toString(x_28);
lean::dec(x_28);
x_42 = lean::string_append(x_40, x_41);
lean::dec(x_41);
x_43 = lean::cnstr_get(x_38, 2);
lean::inc(x_43);
lean::dec(x_38);
x_44 = l_Lean_Parser_Substring_toString(x_43);
lean::dec(x_43);
x_45 = lean::string_append(x_42, x_44);
lean::dec(x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
return x_46;
}
}
}
case 2:
{
obj* x_47; obj* x_48; obj* x_49; uint8 x_50; 
x_47 = lean::cnstr_get(x_1, 0);
lean::inc(x_47);
lean::dec(x_1);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = l_Lean_Parser_choice;
x_50 = lean_name_dec_eq(x_48, x_49);
lean::dec(x_48);
if (x_50 == 0)
{
obj* x_51; obj* x_52; 
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_52 = l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; 
lean::dec(x_52);
x_53 = lean::box(0);
return x_53;
}
else
{
uint8 x_54; 
x_54 = !lean::is_exclusive(x_52);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; 
x_55 = lean::cnstr_get(x_52, 0);
x_56 = l_String_splitAux___main___closed__1;
x_57 = l_List_foldl___main___at_String_join___spec__1(x_56, x_55);
lean::dec(x_55);
lean::cnstr_set(x_52, 0, x_57);
return x_52;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_52, 0);
lean::inc(x_58);
lean::dec(x_52);
x_59 = l_String_splitAux___main___closed__1;
x_60 = l_List_foldl___main___at_String_join___spec__1(x_59, x_58);
lean::dec(x_58);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
obj* x_62; 
x_62 = lean::cnstr_get(x_47, 1);
lean::inc(x_62);
lean::dec(x_47);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; 
lean::dec(x_62);
x_63 = lean::box(0);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_66 = l_Lean_Parser_Syntax_reprint___main(x_64);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; 
lean::dec(x_66);
lean::dec(x_65);
x_67 = lean::box(0);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
lean::dec(x_66);
x_69 = l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1(x_65);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; 
lean::dec(x_69);
lean::dec(x_68);
x_70 = lean::box(0);
return x_70;
}
else
{
uint8 x_71; 
x_71 = !lean::is_exclusive(x_69);
if (x_71 == 0)
{
obj* x_72; uint8 x_73; uint8 x_74; 
x_72 = lean::cnstr_get(x_69, 0);
x_73 = 1;
x_74 = l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2(x_68, x_73, x_72);
lean::dec(x_72);
if (x_74 == 0)
{
obj* x_75; 
lean::free_heap_obj(x_69);
lean::dec(x_68);
x_75 = lean::box(0);
return x_75;
}
else
{
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
}
else
{
obj* x_76; uint8 x_77; uint8 x_78; 
x_76 = lean::cnstr_get(x_69, 0);
lean::inc(x_76);
lean::dec(x_69);
x_77 = 1;
x_78 = l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2(x_68, x_77, x_76);
lean::dec(x_76);
if (x_78 == 0)
{
obj* x_79; 
lean::dec(x_68);
x_79 = lean::box(0);
return x_79;
}
else
{
obj* x_80; 
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_68);
return x_80;
}
}
}
}
}
}
}
default: 
{
obj* x_81; 
lean::dec(x_1);
x_81 = l_Lean_Parser_Syntax_reprint___main___closed__1;
return x_81;
}
}
}
}
obj* l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_List_foldr___main___at_Lean_Parser_Syntax_reprint___main___spec__2(x_1, x_4, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_Parser_Syntax_reprint(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_reprint___main(x_1);
return x_2;
}
}
obj* l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_Name_toStringWithSep___main(x_2, x_1);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__3(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(x_4);
x_7 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__3(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(x_8);
x_11 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__3(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__4(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__5(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__4(x_4);
x_7 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__5(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__4(x_8);
x_11 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__5(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(obj* x_1, obj* x_2) {
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
x_9 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_4, x_2);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_Parser_Syntax_format___main(x_4);
x_7 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_Lean_Parser_Syntax_format___main(x_8);
x_11 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__8(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Nat_repr(x_5);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = l_Nat_repr(x_8);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = 0;
lean::inc(x_2);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_2);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_11);
x_13 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__8(x_4, x_2);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_11);
return x_14;
}
}
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("`");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("{");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("}");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("{");
x_2 = lean::string_length(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("noKind");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_Syntax_format___main___closed__8() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("<missing>");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_Syntax_format___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_4 = l_String_quote(x_3);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
case 1:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 3);
lean::inc(x_7);
x_8 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__3(x_7);
x_9 = lean::cnstr_get(x_6, 4);
lean::inc(x_9);
x_10 = l_List_reverse___rarg(x_9);
x_11 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__5(x_10);
x_12 = l_List_append___rarg(x_8, x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(x_13);
x_15 = 0;
x_16 = l_Lean_Parser_Syntax_format___main___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_12);
x_18 = l_Lean_Parser_Syntax_format___main___closed__2;
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_15);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = l_Lean_formatKVMap___closed__1;
x_21 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_12, x_20);
lean::dec(x_12);
x_22 = l_Lean_Parser_Syntax_format___main___closed__3;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_15);
x_24 = l_Lean_Parser_Syntax_format___main___closed__4;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_15);
x_26 = l_Lean_Parser_Syntax_format___main___closed__5;
x_27 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Format_group___main(x_27);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_17);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_15);
return x_29;
}
}
case 2:
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_30, 2);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
x_33 = l_Lean_Parser_Syntax_format___main___closed__6;
x_34 = lean_name_dec_eq(x_32, x_33);
if (lean::obj_tag(x_31) == 0)
{
lean::dec(x_31);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_35 = l_Lean_Parser_Syntax_format___main___closed__7;
x_36 = lean::box(0);
x_37 = l_Lean_Name_replacePrefix___main(x_32, x_35, x_36);
x_38 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(x_37);
x_39 = 0;
x_40 = l_Lean_Parser_Syntax_format___main___closed__2;
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_39);
x_42 = lean::cnstr_get(x_30, 1);
lean::inc(x_42);
lean::dec(x_30);
x_43 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_42);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_43);
x_45 = lean::box(1);
x_46 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_44, x_45);
lean::dec(x_44);
x_47 = l_Lean_Format_paren___closed__1;
x_48 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_46);
lean::cnstr_set_scalar(x_48, sizeof(void*)*2, x_39);
x_49 = l_Lean_Format_paren___closed__2;
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_39);
x_51 = l_Lean_Format_paren___closed__3;
x_52 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_50);
x_53 = l_Lean_Format_group___main(x_52);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_32);
x_54 = lean::cnstr_get(x_30, 1);
lean::inc(x_54);
lean::dec(x_30);
x_55 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_54);
x_56 = lean::box(1);
x_57 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_55, x_56);
lean::dec(x_55);
x_58 = 0;
x_59 = l_Lean_Parser_Syntax_format___main___closed__2;
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_57);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_58);
x_61 = l_Lean_Format_sbracket___closed__1;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_60);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_58);
x_63 = l_Lean_Format_sbracket___closed__2;
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_58);
x_65 = l_Lean_Format_sbracket___closed__3;
x_66 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_64);
x_67 = l_Lean_Format_group___main(x_66);
return x_67;
}
}
else
{
obj* x_68; uint8 x_69; 
lean::inc(x_31);
x_68 = l_List_reverse___rarg(x_31);
x_69 = !lean::is_exclusive(x_31);
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_70 = lean::cnstr_get(x_31, 1);
lean::dec(x_70);
x_71 = lean::cnstr_get(x_31, 0);
lean::dec(x_71);
x_72 = l_Lean_formatKVMap___closed__1;
x_73 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__8(x_68, x_72);
x_74 = 0;
x_75 = l_Lean_Parser_Syntax_format___main___closed__3;
x_76 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_73);
lean::cnstr_set_scalar(x_76, sizeof(void*)*2, x_74);
x_77 = l_Lean_Parser_Syntax_format___main___closed__4;
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_74);
x_79 = l_Lean_Parser_Syntax_format___main___closed__5;
x_80 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
x_81 = l_Lean_Format_group___main(x_80);
if (x_34 == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_82 = l_Lean_Parser_Syntax_format___main___closed__7;
x_83 = lean::box(0);
x_84 = l_Lean_Name_replacePrefix___main(x_32, x_82, x_83);
x_85 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(x_84);
x_86 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_81);
lean::cnstr_set_scalar(x_86, sizeof(void*)*2, x_74);
x_87 = lean::cnstr_get(x_30, 1);
lean::inc(x_87);
lean::dec(x_30);
x_88 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_87);
lean::cnstr_set(x_31, 1, x_88);
lean::cnstr_set(x_31, 0, x_86);
x_89 = lean::box(1);
x_90 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_31, x_89);
lean::dec(x_31);
x_91 = l_Lean_Format_paren___closed__1;
x_92 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
lean::cnstr_set_scalar(x_92, sizeof(void*)*2, x_74);
x_93 = l_Lean_Format_paren___closed__2;
x_94 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_93);
lean::cnstr_set_scalar(x_94, sizeof(void*)*2, x_74);
x_95 = l_Lean_Format_paren___closed__3;
x_96 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_94);
x_97 = l_Lean_Format_group___main(x_96);
return x_97;
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::free_heap_obj(x_31);
lean::dec(x_32);
x_98 = lean::cnstr_get(x_30, 1);
lean::inc(x_98);
lean::dec(x_30);
x_99 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_98);
x_100 = lean::box(1);
x_101 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_99, x_100);
lean::dec(x_99);
x_102 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_102, 0, x_81);
lean::cnstr_set(x_102, 1, x_101);
lean::cnstr_set_scalar(x_102, sizeof(void*)*2, x_74);
x_103 = l_Lean_Format_sbracket___closed__1;
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_102);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_74);
x_105 = l_Lean_Format_sbracket___closed__2;
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_105);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_74);
x_107 = l_Lean_Format_sbracket___closed__3;
x_108 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_106);
x_109 = l_Lean_Format_group___main(x_108);
return x_109;
}
}
else
{
obj* x_110; obj* x_111; uint8 x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_31);
x_110 = l_Lean_formatKVMap___closed__1;
x_111 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__8(x_68, x_110);
x_112 = 0;
x_113 = l_Lean_Parser_Syntax_format___main___closed__3;
x_114 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_111);
lean::cnstr_set_scalar(x_114, sizeof(void*)*2, x_112);
x_115 = l_Lean_Parser_Syntax_format___main___closed__4;
x_116 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_116, 0, x_114);
lean::cnstr_set(x_116, 1, x_115);
lean::cnstr_set_scalar(x_116, sizeof(void*)*2, x_112);
x_117 = l_Lean_Parser_Syntax_format___main___closed__5;
x_118 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_116);
x_119 = l_Lean_Format_group___main(x_118);
if (x_34 == 0)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_120 = l_Lean_Parser_Syntax_format___main___closed__7;
x_121 = lean::box(0);
x_122 = l_Lean_Name_replacePrefix___main(x_32, x_120, x_121);
x_123 = l_Lean_fmt___at_Lean_Parser_Syntax_format___main___spec__2(x_122);
x_124 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_119);
lean::cnstr_set_scalar(x_124, sizeof(void*)*2, x_112);
x_125 = lean::cnstr_get(x_30, 1);
lean::inc(x_125);
lean::dec(x_30);
x_126 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_125);
x_127 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_127, 0, x_124);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::box(1);
x_129 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_127, x_128);
lean::dec(x_127);
x_130 = l_Lean_Format_paren___closed__1;
x_131 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_129);
lean::cnstr_set_scalar(x_131, sizeof(void*)*2, x_112);
x_132 = l_Lean_Format_paren___closed__2;
x_133 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_133, 0, x_131);
lean::cnstr_set(x_133, 1, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*2, x_112);
x_134 = l_Lean_Format_paren___closed__3;
x_135 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_135, 0, x_134);
lean::cnstr_set(x_135, 1, x_133);
x_136 = l_Lean_Format_group___main(x_135);
return x_136;
}
else
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
lean::dec(x_32);
x_137 = lean::cnstr_get(x_30, 1);
lean::inc(x_137);
lean::dec(x_30);
x_138 = l_List_map___main___at_Lean_Parser_Syntax_format___main___spec__7(x_137);
x_139 = lean::box(1);
x_140 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_138, x_139);
lean::dec(x_138);
x_141 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_141, 0, x_119);
lean::cnstr_set(x_141, 1, x_140);
lean::cnstr_set_scalar(x_141, sizeof(void*)*2, x_112);
x_142 = l_Lean_Format_sbracket___closed__1;
x_143 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_141);
lean::cnstr_set_scalar(x_143, sizeof(void*)*2, x_112);
x_144 = l_Lean_Format_sbracket___closed__2;
x_145 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_144);
lean::cnstr_set_scalar(x_145, sizeof(void*)*2, x_112);
x_146 = l_Lean_Format_sbracket___closed__3;
x_147 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_145);
x_148 = l_Lean_Format_group___main(x_147);
return x_148;
}
}
}
}
default: 
{
obj* x_149; 
lean::dec(x_1);
x_149 = l_Lean_Parser_Syntax_format___main___closed__8;
return x_149;
}
}
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_joinSep___main___at_Lean_Parser_Syntax_format___main___spec__6(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_Syntax_format(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_format___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_Lean_HasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Syntax_format), 1, 0);
return x_1;
}
}
obj* l_Lean_fmt___at_Lean_Parser_Syntax_HasToString___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_format___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_Syntax_HasToString() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_HasRepr___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_fmt___at_Lean_Parser_Syntax_HasToString___spec__1), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_parser_parsec(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_syntax(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parsec(w);
if (io_result_is_error(w)) return w;
l_Lean_Parser_choice = _init_l_Lean_Parser_choice();
lean::mark_persistent(l_Lean_Parser_choice);
l_Lean_Parser_noKind = _init_l_Lean_Parser_noKind();
lean::mark_persistent(l_Lean_Parser_noKind);
l_Lean_Parser_MacroScope_DecidableEq = _init_l_Lean_Parser_MacroScope_DecidableEq();
lean::mark_persistent(l_Lean_Parser_MacroScope_DecidableEq);
l_Lean_Parser_MacroScope_Lean_HasFormat = _init_l_Lean_Parser_MacroScope_Lean_HasFormat();
lean::mark_persistent(l_Lean_Parser_MacroScope_Lean_HasFormat);
l_Lean_Parser_Inhabited = _init_l_Lean_Parser_Inhabited();
lean::mark_persistent(l_Lean_Parser_Inhabited);
l_Lean_Parser_Substring_HasToString = _init_l_Lean_Parser_Substring_HasToString();
lean::mark_persistent(l_Lean_Parser_Substring_HasToString);
l_Lean_Parser_Syntax_updateLeading___closed__1 = _init_l_Lean_Parser_Syntax_updateLeading___closed__1();
lean::mark_persistent(l_Lean_Parser_Syntax_updateLeading___closed__1);
l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1 = _init_l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1();
lean::mark_persistent(l_List_mmap___main___at_Lean_Parser_Syntax_reprint___main___spec__1___closed__1);
l_Lean_Parser_Syntax_reprint___main___closed__1 = _init_l_Lean_Parser_Syntax_reprint___main___closed__1();
lean::mark_persistent(l_Lean_Parser_Syntax_reprint___main___closed__1);
l_Lean_Parser_Syntax_format___main___closed__1 = _init_l_Lean_Parser_Syntax_format___main___closed__1();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__1);
l_Lean_Parser_Syntax_format___main___closed__2 = _init_l_Lean_Parser_Syntax_format___main___closed__2();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__2);
l_Lean_Parser_Syntax_format___main___closed__3 = _init_l_Lean_Parser_Syntax_format___main___closed__3();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__3);
l_Lean_Parser_Syntax_format___main___closed__4 = _init_l_Lean_Parser_Syntax_format___main___closed__4();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__4);
l_Lean_Parser_Syntax_format___main___closed__5 = _init_l_Lean_Parser_Syntax_format___main___closed__5();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__5);
l_Lean_Parser_Syntax_format___main___closed__6 = _init_l_Lean_Parser_Syntax_format___main___closed__6();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__6);
l_Lean_Parser_Syntax_format___main___closed__7 = _init_l_Lean_Parser_Syntax_format___main___closed__7();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__7);
l_Lean_Parser_Syntax_format___main___closed__8 = _init_l_Lean_Parser_Syntax_format___main___closed__8();
lean::mark_persistent(l_Lean_Parser_Syntax_format___main___closed__8);
l_Lean_Parser_Syntax_Lean_HasFormat = _init_l_Lean_Parser_Syntax_Lean_HasFormat();
lean::mark_persistent(l_Lean_Parser_Syntax_Lean_HasFormat);
l_Lean_Parser_Syntax_HasToString = _init_l_Lean_Parser_Syntax_HasToString();
lean::mark_persistent(l_Lean_Parser_Syntax_HasToString);
return w;
}

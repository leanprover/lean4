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
obj* l_lean_parser_syntax_is__of__kind___main___boxed(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___boxed(obj*);
obj* l_lean_parser_syntax_is__of__kind___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_parser_syntax_to__format___main___spec__3(obj*);
obj* l_list_map___main___at_lean_parser_syntax_to__format___main___spec__5(obj*);
obj* l_lean_parser_syntax_get__head__info__lst___boxed(obj*);
extern obj* l_lean_format_paren___closed__1;
obj* l_lean_parser_macro__scope;
obj* l_lean_parser_syntax_as__node(obj*);
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__2(obj*, obj*, obj*);
obj* l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__4;
extern obj* l_lean_parser_monad__parsec_sep__by1___rarg___closed__1;
obj* l_lean_parser_syntax_reprint__atom___main___boxed(obj*);
obj* l_lean_parser_macro__scope_decidable__eq;
obj* l_lean_parser_syntax_reprint(obj*);
obj* l_lean_parser_syntax_get__head__info___boxed(obj*);
obj* l_lean_parser_syntax_flip__scopes___main(obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__1;
obj* l_lean_parser_syntax_get__head__info__lst(obj*);
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_parser_syntax_reprint__atom___main(obj*);
obj* l_lean_nat__has__to__format(obj*);
obj* l_lean_parser_syntax_to__format__lst(obj*);
obj* l_lean_has__repr___lambda__1(obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_string_quote(obj*);
obj* l_lean_parser_syntax_update__leading___closed__1;
obj* l_lean_parser_macro__scopes_flip___boxed(obj*, obj*);
obj* l_lean_parser_macro__scopes;
obj* l_lean_parser_syntax_mreplace__lst___boxed(obj*);
obj* l_lean_parser_syntax_to__format___main___closed__7;
namespace lean {
obj* string_length(obj*);
}
obj* l_lean_parser_syntax_mreplace__lst___main(obj*);
obj* l_option_orelse___main___rarg(obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_syntax_mreplace(obj*);
obj* l_lean_parser_syntax_to__format___main___closed__6;
obj* l_lean_parser_syntax_reprint__lst(obj*);
extern obj* l_lean_format_sbracket___closed__2;
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__1(obj*);
obj* l_lean_parser_syntax_mreplace___main___rarg(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_syntax_as__node___main___spec__1(obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__5;
obj* l_lean_name_replace__prefix___main(obj*, obj*, obj*);
obj* l_lean_parser_syntax_get__pos(obj*);
namespace lean {
obj* string_iterator_to_end(obj*);
}
namespace lean {
obj* string_iterator_extract(obj*, obj*);
}
obj* l_lean_parser_syntax_to__format___main___closed__9;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_name_to__string__with__sep___main(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string___boxed(obj*);
obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_syntax_mreplace__lst(obj*);
obj* l_lean_parser_syntax_get__head__info__lst___main(obj*);
obj* l_lean_parser_syntax_has__to__string;
obj* l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__8;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_syntax_flip__scopes(obj*, obj*);
obj* l_string_iterator_nextn___main(obj*, obj*);
extern obj* l_lean_format_sbracket___closed__1;
obj* l_nat_dec__eq___boxed(obj*, obj*);
obj* l_lean_parser_syntax_to__format(obj*);
obj* l_lean_parser_inhabited;
obj* l_lean_parser_syntax_to__format___main(obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(obj*);
obj* l_list_foldl___main___at_string_join___spec__1(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_syntax_update__leading(obj*, obj*);
obj* l_lean_parser_syntax_to__format__lst___main(obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_substring_has__to__string;
obj* l_lean_parser_syntax_reprint___main(obj*);
obj* l_lean_parser_syntax_mreplace__lst___main___rarg(obj*, obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main(obj*);
obj* l_lean_parser_syntax_reprint__lst___main(obj*);
obj* l_lean_parser_syntax_get__head__info__lst___main___boxed(obj*);
obj* l_lean_parser_syntax_mreplace__lst___main___boxed(obj*);
obj* l_lean_parser_syntax_kind(obj*);
obj* l_lean_parser_syntax_lean_has__to__format;
obj* l_lean_format_group___main(obj*);
obj* l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___boxed(obj*);
extern obj* l_lean_format_paren___closed__3;
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_lean_parser_syntax_mreplace__lst___rarg(obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_syntax_kind___main(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_to__fmt___at_lean_parser_syntax_has__to__string___spec__1(obj*);
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__7___boxed(obj*);
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_syntax_reprint__atom(obj*);
obj* l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(obj*, obj*);
obj* l_lean_parser_syntax_reprint__lst___main___closed__1;
obj* l_lean_parser_syntax_to__format___main___closed__2;
obj* l_lean_parser_macro__scope_lean_has__to__format;
namespace lean {
obj* string_mk_iterator(obj*);
}
extern obj* l_lean_format_paren___closed__2;
obj* l_lean_parser_macro__scopes_flip___main(obj*, obj*);
obj* l_lean_parser_syntax_list(obj*);
obj* l_lean_parser_macro__scopes_flip(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__1___boxed(obj*, obj*, obj*);
extern obj* l_lean_format_sbracket___closed__3;
obj* l_lean_parser_syntax_get__head__info(obj*);
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(obj*);
uint8 l_lean_parser_syntax_is__of__kind(obj*, obj*);
obj* l_lean_parser_syntax_replace(obj*, obj*);
obj* l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(obj*, obj*);
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__7(obj*);
obj* l_nat_repr(obj*);
obj* l_lean_parser_choice;
obj* l_lean_parser_syntax_reprint___main___closed__1;
obj* l_lean_parser_syntax_get__pos___boxed(obj*);
obj* l___private_init_lean_parser_syntax_1__update__leading__aux(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_syntax_get__head__info___main___boxed(obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l___private_init_lean_parser_syntax_1__update__leading__aux___main(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___rarg(obj*, obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__3;
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_syntax_get__head__info___main(obj*);
obj* l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1___boxed(obj*, obj*);
obj* l_lean_parser_macro__scopes_flip___main___boxed(obj*, obj*);
obj* l_lean_parser_syntax_reprint__atom___boxed(obj*);
obj* _init_l_lean_parser_choice() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("choice");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_no__kind() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("no_kind");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_macro__scope_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_lean_parser_macro__scope_lean_has__to__format() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_nat__has__to__format), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_macro__scope() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_macro__scopes() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(3);
return x_0;
}
}
obj* l_lean_parser_substring_to__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::string_iterator_extract(x_1, x_2);
x_4 = l_string_join___closed__1;
x_5 = l_option_get__or__else___main___rarg(x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_parser_substring_to__string___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_substring_to__string(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_substring_of__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = lean::string_mk_iterator(x_0);
lean::inc(x_1);
x_3 = lean::string_iterator_to_end(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_substring_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_substring_to__string___boxed), 1, 0);
return x_0;
}
}
obj* l_lean_parser_macro__scopes_flip___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l_lean_parser_macro__scopes_flip___main(x_0, x_5);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_3);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_12; uint8 x_14; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
x_14 = lean::nat_dec_eq(x_3, x_10);
lean::dec(x_10);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_12);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
else
{
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_3);
return x_12;
}
}
}
}
}
obj* l_lean_parser_macro__scopes_flip___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_macro__scopes_flip___main(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_macro__scopes_flip(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_macro__scopes_flip___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_macro__scopes_flip___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_macro__scopes_flip(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_syntax_flip__scopes___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 4);
lean::inc(x_13);
lean::dec(x_2);
x_16 = l_lean_parser_macro__scopes_flip___main(x_13, x_0);
lean::dec(x_13);
x_18 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_7);
lean::cnstr_set(x_18, 2, x_9);
lean::cnstr_set(x_18, 3, x_11);
lean::cnstr_set(x_18, 4, x_16);
if (lean::is_scalar(x_4)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_4;
}
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
case 2:
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_32; obj* x_33; 
x_20 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_22 = x_1;
} else {
 lean::inc(x_20);
 lean::dec(x_1);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 2);
lean::inc(x_27);
lean::dec(x_20);
x_30 = l_lean_parser_macro__scopes_flip___main(x_27, x_0);
lean::dec(x_27);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_23);
lean::cnstr_set(x_32, 1, x_25);
lean::cnstr_set(x_32, 2, x_30);
if (lean::is_scalar(x_22)) {
 x_33 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_33 = x_22;
}
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
default:
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l_lean_parser_syntax_flip__scopes(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_syntax_flip__scopes___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_syntax_mk__node(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_list_map___main___at_lean_parser_syntax_as__node___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = l_lean_parser_syntax_flip__scopes___main(x_9, x_4);
x_12 = l_list_map___main___at_lean_parser_syntax_as__node___main___spec__1(x_0, x_6);
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
}
obj* l_lean_parser_syntax_as__node___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_1; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = l_list_map___main___at_lean_parser_syntax_as__node___main___spec__1(x_1, x_6);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_8);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
case 3:
{
obj* x_12; 
x_12 = lean::box(0);
return x_12;
}
default:
{
obj* x_14; 
lean::dec(x_0);
x_14 = lean::box(0);
return x_14;
}
}
}
}
obj* l_lean_parser_syntax_as__node(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_list(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_no__kind;
x_2 = l_lean_parser_syntax_mk__node(x_1, x_0);
return x_2;
}
}
obj* l_lean_parser_syntax_kind___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_1; obj* x_4; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
case 3:
{
obj* x_8; 
x_8 = lean::box(0);
return x_8;
}
default:
{
obj* x_10; 
lean::dec(x_0);
x_10 = lean::box(0);
return x_10;
}
}
}
}
obj* l_lean_parser_syntax_kind(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_kind___main(x_0);
return x_1;
}
}
uint8 l_lean_parser_syntax_is__of__kind___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean_name_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
default:
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
}
obj* l_lean_parser_syntax_is__of__kind___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_parser_syntax_is__of__kind___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_lean_parser_syntax_is__of__kind(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_parser_syntax_is__of__kind___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_syntax_is__of__kind___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_parser_syntax_is__of__kind(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_option_get__or__else___main___rarg(x_2, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_11);
x_15 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::apply_2(x_6, lean::box(0), x_15);
return x_16;
}
}
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::inc(x_1);
x_8 = l_lean_parser_syntax_mreplace__lst___main___rarg(x_1, x_2, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__2), 3, 2);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_0);
x_10 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_23; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::apply_2(x_20, lean::box(0), x_14);
return x_23;
}
}
}
obj* l_lean_parser_syntax_mreplace___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::inc(x_1);
x_10 = lean::apply_1(x_1, x_2);
lean::inc(x_7);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__3), 5, 4);
lean::closure_set(x_12, 0, x_5);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
lean::closure_set(x_12, 3, x_7);
x_13 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
default:
{
obj* x_14; 
x_14 = lean::box(0);
x_3 = x_14;
goto lbl_4;
}
}
lbl_4:
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::inc(x_2);
x_19 = lean::apply_1(x_1, x_2);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_20, 0, x_0);
lean::closure_set(x_20, 1, x_2);
x_21 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
}
}
obj* l_lean_parser_syntax_mreplace___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace__lst___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_10; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::apply_2(x_7, lean::box(0), x_2);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 2);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
lean::dec(x_16);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
lean::inc(x_1);
lean::inc(x_0);
x_28 = l_lean_parser_syntax_mreplace___main___rarg(x_0, x_1, x_11);
x_29 = l_lean_parser_monad__parsec_sep__by1___rarg___closed__1;
x_30 = lean::apply_4(x_23, lean::box(0), lean::box(0), x_29, x_28);
x_31 = l_lean_parser_syntax_mreplace__lst___main___rarg(x_0, x_1, x_13);
x_32 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_30, x_31);
return x_32;
}
}
}
obj* l_lean_parser_syntax_mreplace__lst___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace__lst___main___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_syntax_mreplace___main___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_syntax_mreplace___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_mreplace___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace__lst___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_mreplace__lst___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_syntax_mreplace___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_parser_syntax_mreplace(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_mreplace(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace__lst___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_syntax_mreplace__lst___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_parser_syntax_mreplace__lst(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace__lst___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace__lst___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_mreplace__lst(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_7 = x_1;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
lean::inc(x_0);
x_9 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_0, x_3);
x_10 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_2; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = lean::apply_1(x_0, x_1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
} else {
 lean::dec(x_1);
 x_7 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(x_0, x_8);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 2);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_13);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
obj* x_21; 
lean::dec(x_2);
lean::dec(x_0);
lean::dec(x_7);
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
lean::dec(x_6);
return x_21;
}
}
case 3:
{
obj* x_24; obj* x_25; 
x_24 = lean::apply_1(x_0, x_1);
x_25 = l_option_get__or__else___main___rarg(x_24, x_1);
lean::dec(x_24);
return x_25;
}
default:
{
obj* x_28; obj* x_29; 
lean::inc(x_1);
x_28 = lean::apply_1(x_0, x_1);
x_29 = l_option_get__or__else___main___rarg(x_28, x_1);
lean::dec(x_1);
lean::dec(x_28);
return x_29;
}
}
}
}
obj* l_lean_parser_syntax_replace(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_replace___spec__1(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_syntax_1__update__leading__aux___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_4);
lean::dec(x_2);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_11 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
} else {
 lean::inc(x_11);
 lean::dec(x_2);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_16 = x_5;
} else {
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
lean::dec(x_14);
x_24 = lean::string_iterator_offset(x_1);
x_25 = lean::nat_sub(x_21, x_24);
lean::dec(x_24);
lean::inc(x_1);
x_28 = l_string_iterator_nextn___main(x_1, x_25);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_21);
lean::cnstr_set(x_30, 2, x_17);
if (lean::is_scalar(x_16)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_16;
}
lean::cnstr_set(x_31, 0, x_30);
if (lean::is_scalar(x_13)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_13;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
if (lean::is_scalar(x_4)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_4;
}
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_19);
return x_35;
}
}
case 1:
{
obj* x_36; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; obj* x_44; 
lean::dec(x_38);
lean::dec(x_36);
x_43 = lean::box(0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_1);
return x_44;
}
else
{
obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_45 = lean::cnstr_get(x_36, 1);
x_47 = lean::cnstr_get(x_36, 2);
x_49 = lean::cnstr_get(x_36, 3);
x_51 = lean::cnstr_get(x_36, 4);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_53 = x_36;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::inc(x_49);
 lean::inc(x_51);
 lean::dec(x_36);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_56 = x_39;
} else {
 lean::inc(x_54);
 lean::dec(x_39);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 2);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_57, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_54, 1);
lean::inc(x_61);
lean::dec(x_54);
x_64 = lean::string_iterator_offset(x_1);
x_65 = lean::nat_sub(x_61, x_64);
lean::dec(x_64);
lean::inc(x_1);
x_68 = l_string_iterator_nextn___main(x_1, x_65);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_1);
lean::cnstr_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_61);
lean::cnstr_set(x_70, 2, x_57);
if (lean::is_scalar(x_56)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_56;
}
lean::cnstr_set(x_71, 0, x_70);
if (lean::is_scalar(x_53)) {
 x_72 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_72 = x_53;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_45);
lean::cnstr_set(x_72, 2, x_47);
lean::cnstr_set(x_72, 3, x_49);
lean::cnstr_set(x_72, 4, x_51);
if (lean::is_scalar(x_38)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_38;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_59);
return x_75;
}
}
case 2:
{
obj* x_77; obj* x_78; 
lean::dec(x_0);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_1);
return x_78;
}
default:
{
obj* x_79; obj* x_80; 
x_79 = lean::box(0);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_1);
return x_80;
}
}
}
}
obj* l___private_init_lean_parser_syntax_1__update__leading__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_syntax_1__update__leading__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_5 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_9 = x_1;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_1);
 x_9 = lean::box(0);
}
lean::inc(x_0);
x_11 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(x_0, x_5, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(x_0, x_7, x_14);
x_18 = lean::cnstr_get(x_17, 0);
x_20 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_22 = x_17;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_9;
}
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_18);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_20);
return x_24;
}
}
}
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_5; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_9 = lean::apply_2(x_0, x_1, x_2);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_10 = x_1;
} else {
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
x_13 = lean::cnstr_get(x_9, 1);
lean::inc(x_13);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_5, 1);
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(x_0, x_16, x_13);
x_19 = lean::cnstr_get(x_18, 0);
x_21 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 x_23 = x_18;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_18);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_5, 2);
lean::inc(x_26);
lean::dec(x_5);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_19);
lean::cnstr_set(x_29, 2, x_26);
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_30 = x_10;
}
lean::cnstr_set(x_30, 0, x_29);
if (lean::is_scalar(x_23)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_23;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_21);
return x_31;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_41; 
lean::dec(x_5);
lean::dec(x_10);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_37 = x_9;
} else {
 lean::inc(x_35);
 lean::dec(x_9);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_11, 0);
lean::inc(x_38);
lean::dec(x_11);
if (lean::is_scalar(x_37)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_37;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_35);
return x_41;
}
}
default:
{
obj* x_42; 
x_42 = lean::box(0);
x_3 = x_42;
goto lbl_4;
}
}
lbl_4:
{
obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_54; 
lean::dec(x_3);
lean::inc(x_1);
x_45 = lean::apply_2(x_0, x_1, x_2);
x_46 = lean::cnstr_get(x_45, 0);
x_48 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 x_50 = x_45;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_45);
 x_50 = lean::box(0);
}
x_51 = l_option_get__or__else___main___rarg(x_46, x_1);
lean::dec(x_1);
lean::dec(x_46);
if (lean::is_scalar(x_50)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_50;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_48);
return x_54;
}
}
}
obj* _init_l_lean_parser_syntax_update__leading___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_syntax_1__update__leading__aux), 2, 0);
return x_0;
}
}
obj* l_lean_parser_syntax_update__leading(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_lean_parser_syntax_update__leading___closed__1;
x_4 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_syntax_get__head__info___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_1, 1);
x_3 = l_lean_parser_syntax_get__head__info__lst___main(x_2);
return x_3;
}
case 3:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
default:
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
return x_6;
}
}
}
}
obj* l_lean_parser_syntax_get__head__info__lst___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = l_lean_parser_syntax_get__head__info___main(x_2);
x_5 = l_lean_parser_syntax_get__head__info__lst___main(x_3);
x_6 = l_option_orelse___main___rarg(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
return x_6;
}
}
}
obj* l_lean_parser_syntax_get__head__info___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_get__head__info__lst___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info__lst___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_get__head__info(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info___main(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_get__head__info___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_get__head__info__lst(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info__lst___main(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_get__head__info__lst___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info__lst(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_get__pos(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::is_scalar(x_5)) {
 x_9 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_9 = x_5;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
}
}
obj* l_lean_parser_syntax_get__pos___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__pos(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_reprint__atom___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_5, 0);
x_7 = l_lean_parser_substring_to__string(x_6);
x_8 = lean::string_append(x_7, x_4);
x_9 = lean::cnstr_get(x_5, 2);
x_10 = l_lean_parser_substring_to__string(x_9);
x_11 = lean::string_append(x_8, x_10);
lean::dec(x_10);
return x_11;
}
}
}
obj* l_lean_parser_syntax_reprint__atom___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint__atom___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_reprint__atom(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint__atom___main(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_reprint__atom___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint__atom(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; obj* x_3; 
x_2 = 1;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::string_dec_eq(x_4, x_0);
if (x_6 == 0)
{
uint8 x_7; obj* x_8; 
x_7 = 0;
x_8 = lean::box(x_7);
return x_8;
}
else
{
x_1 = x_5;
goto _start;
}
}
}
}
obj* _init_l_lean_parser_syntax_reprint___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("");
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_reprint___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_27; obj* x_29; 
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_15 = x_4;
} else {
 lean::inc(x_13);
 lean::dec(x_4);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = l_lean_parser_substring_to__string(x_16);
lean::dec(x_16);
x_20 = lean::string_append(x_18, x_10);
lean::dec(x_10);
x_22 = lean::cnstr_get(x_13, 2);
lean::inc(x_22);
lean::dec(x_13);
x_25 = l_lean_parser_substring_to__string(x_22);
lean::dec(x_22);
x_27 = lean::string_append(x_20, x_25);
lean::dec(x_25);
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_27);
return x_29;
}
}
case 1:
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_30, 1);
lean::inc(x_35);
lean::dec(x_30);
x_38 = l_lean_parser_substring_to__string(x_35);
lean::dec(x_35);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_38);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_58; obj* x_60; obj* x_62; 
x_41 = lean::cnstr_get(x_30, 1);
lean::inc(x_41);
lean::dec(x_30);
x_44 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_46 = x_33;
} else {
 lean::inc(x_44);
 lean::dec(x_33);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
x_49 = l_lean_parser_substring_to__string(x_47);
lean::dec(x_47);
x_51 = l_lean_parser_substring_to__string(x_41);
lean::dec(x_41);
x_53 = lean::string_append(x_49, x_51);
lean::dec(x_51);
x_55 = lean::cnstr_get(x_44, 2);
lean::inc(x_55);
lean::dec(x_44);
x_58 = l_lean_parser_substring_to__string(x_55);
lean::dec(x_55);
x_60 = lean::string_append(x_53, x_58);
lean::dec(x_58);
if (lean::is_scalar(x_46)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_46;
}
lean::cnstr_set(x_62, 0, x_60);
return x_62;
}
}
case 2:
{
obj* x_63; obj* x_66; obj* x_68; uint8 x_69; 
x_63 = lean::cnstr_get(x_0, 0);
lean::inc(x_63);
lean::dec(x_0);
x_66 = lean::cnstr_get(x_63, 0);
lean::inc(x_66);
x_68 = l_lean_parser_choice;
x_69 = lean_name_dec_eq(x_66, x_68);
lean::dec(x_66);
if (x_69 == 0)
{
obj* x_71; obj* x_74; 
x_71 = lean::cnstr_get(x_63, 1);
lean::inc(x_71);
lean::dec(x_63);
x_74 = l_lean_parser_syntax_reprint__lst___main(x_71);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; 
x_75 = lean::box(0);
return x_75;
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; 
x_76 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_78 = x_74;
} else {
 lean::inc(x_76);
 lean::dec(x_74);
 x_78 = lean::box(0);
}
x_79 = l_string_join___closed__1;
x_80 = l_list_foldl___main___at_string_join___spec__1(x_79, x_76);
lean::dec(x_76);
if (lean::is_scalar(x_78)) {
 x_82 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_82 = x_78;
}
lean::cnstr_set(x_82, 0, x_80);
return x_82;
}
}
else
{
obj* x_83; 
x_83 = lean::cnstr_get(x_63, 1);
lean::inc(x_83);
lean::dec(x_63);
if (lean::obj_tag(x_83) == 0)
{
obj* x_86; 
x_86 = lean::box(0);
return x_86;
}
else
{
obj* x_87; obj* x_89; obj* x_92; 
x_87 = lean::cnstr_get(x_83, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_83, 1);
lean::inc(x_89);
lean::dec(x_83);
x_92 = l_lean_parser_syntax_reprint___main(x_87);
if (lean::obj_tag(x_92) == 0)
{
obj* x_94; 
lean::dec(x_89);
x_94 = lean::box(0);
return x_94;
}
else
{
obj* x_95; obj* x_98; 
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
lean::dec(x_92);
x_98 = l_lean_parser_syntax_reprint__lst___main(x_89);
if (lean::obj_tag(x_98) == 0)
{
obj* x_100; 
lean::dec(x_95);
x_100 = lean::box(0);
return x_100;
}
else
{
obj* x_101; obj* x_103; obj* x_104; uint8 x_106; 
x_101 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_set(x_98, 0, lean::box(0));
 x_103 = x_98;
} else {
 lean::inc(x_101);
 lean::dec(x_98);
 x_103 = lean::box(0);
}
x_104 = l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(x_95, x_101);
lean::dec(x_101);
x_106 = lean::unbox(x_104);
if (x_106 == 0)
{
obj* x_109; 
lean::dec(x_103);
lean::dec(x_95);
x_109 = lean::box(0);
return x_109;
}
else
{
obj* x_110; 
if (lean::is_scalar(x_103)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_103;
}
lean::cnstr_set(x_110, 0, x_95);
return x_110;
}
}
}
}
}
}
default:
{
obj* x_111; 
x_111 = l_lean_parser_syntax_reprint___main___closed__1;
return x_111;
}
}
}
}
obj* _init_l_lean_parser_syntax_reprint__lst___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_reprint__lst___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint__lst___main___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_lean_parser_syntax_reprint___main(x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; 
lean::dec(x_6);
lean::dec(x_4);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
x_14 = l_lean_parser_syntax_reprint__lst___main(x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
lean::dec(x_11);
lean::dec(x_6);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_6;
}
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_18);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
obj* l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_syntax_reprint(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint___main(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_reprint__lst(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_reprint__lst___main(x_0);
return x_1;
}
}
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_name_to__string___closed__1;
x_2 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_3 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_list_map___main___at_lean_parser_syntax_to__format___main___spec__3(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_2);
x_8 = l_list_map___main___at_lean_parser_syntax_to__format___main___spec__3(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_nat_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_list_map___main___at_lean_parser_syntax_to__format___main___spec__5(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_2);
x_8 = l_list_map___main___at_lean_parser_syntax_to__format___main___spec__5(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__7(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(obj* x_0, obj* x_1) {
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
x_17 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_4, x_1);
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
obj* l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(obj* x_0, obj* x_1) {
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
obj* x_7; obj* x_10; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_7);
return x_10;
}
else
{
obj* x_11; obj* x_14; uint8 x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_11);
x_15 = 0;
lean::inc(x_1);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
x_18 = x_17;
x_19 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(x_4, x_1);
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_15);
x_21 = x_20;
return x_21;
}
}
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("`");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(", ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("{");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("}");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("{");
x_1 = lean::string_length(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("no_kind");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_syntax_to__format___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("<missing>");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_to__format___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_4; obj* x_7; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_string_quote(x_4);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
case 1:
{
obj* x_9; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 3);
lean::inc(x_12);
x_14 = l_list_map___main___at_lean_parser_syntax_to__format___main___spec__3(x_12);
x_15 = lean::cnstr_get(x_9, 4);
lean::inc(x_15);
x_17 = l_list_reverse___rarg(x_15);
x_18 = l_list_map___main___at_lean_parser_syntax_to__format___main___spec__5(x_17);
x_19 = l_list_append___rarg(x_14, x_18);
x_20 = lean::cnstr_get(x_9, 2);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_20);
x_24 = 0;
x_25 = l_lean_parser_syntax_to__format___main___closed__1;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_24);
x_27 = x_26;
if (lean::obj_tag(x_19) == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_lean_parser_syntax_to__format___main___closed__2;
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_24);
x_30 = x_29;
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_31 = l_lean_parser_syntax_to__format___main___closed__3;
x_32 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_19, x_31);
x_33 = l_lean_parser_syntax_to__format___main___closed__4;
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_24);
x_35 = x_34;
x_36 = l_lean_parser_syntax_to__format___main___closed__5;
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_24);
x_38 = x_37;
x_39 = l_lean_parser_syntax_to__format___main___closed__6;
x_40 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_38);
x_41 = l_lean_format_group___main(x_40);
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_27);
lean::cnstr_set(x_42, 1, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_24);
x_43 = x_42;
return x_43;
}
}
case 2:
{
obj* x_44; obj* x_47; obj* x_49; obj* x_51; uint8 x_52; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
x_47 = lean::cnstr_get(x_44, 2);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
x_51 = l_lean_parser_syntax_to__format___main___closed__7;
x_52 = lean_name_dec_eq(x_49, x_51);
if (lean::obj_tag(x_47) == 0)
{
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_53 = l_lean_parser_syntax_to__format___main___closed__8;
x_54 = lean::box(0);
x_55 = l_lean_name_replace__prefix___main(x_49, x_53, x_54);
x_56 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_55);
x_57 = 0;
x_58 = l_lean_parser_syntax_to__format___main___closed__2;
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_57);
x_60 = x_59;
x_61 = lean::cnstr_get(x_44, 1);
lean::inc(x_61);
lean::dec(x_44);
x_64 = l_lean_parser_syntax_to__format__lst___main(x_61);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_60);
lean::cnstr_set(x_65, 1, x_64);
x_66 = lean::box(1);
x_67 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_65, x_66);
x_68 = l_lean_format_paren___closed__1;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_57);
x_70 = x_69;
x_71 = l_lean_format_paren___closed__2;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_57);
x_73 = x_72;
x_74 = l_lean_format_paren___closed__3;
x_75 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_73);
x_76 = l_lean_format_group___main(x_75);
return x_76;
}
else
{
obj* x_78; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_49);
x_78 = lean::cnstr_get(x_44, 1);
lean::inc(x_78);
lean::dec(x_44);
x_81 = l_lean_parser_syntax_to__format__lst___main(x_78);
x_82 = lean::box(1);
x_83 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_81, x_82);
x_84 = 0;
x_85 = l_lean_parser_syntax_to__format___main___closed__2;
x_86 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_83);
lean::cnstr_set_scalar(x_86, sizeof(void*)*2, x_84);
x_87 = x_86;
x_88 = l_lean_format_sbracket___closed__1;
x_89 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_87);
lean::cnstr_set_scalar(x_89, sizeof(void*)*2, x_84);
x_90 = x_89;
x_91 = l_lean_format_sbracket___closed__2;
x_92 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*2, x_84);
x_93 = x_92;
x_94 = l_lean_format_sbracket___closed__3;
x_95 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_93);
x_96 = l_lean_format_group___main(x_95);
return x_96;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::inc(x_47);
x_98 = l_list_reverse___rarg(x_47);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_99 = x_47;
} else {
 lean::dec(x_47);
 x_99 = lean::box(0);
}
x_100 = l_lean_parser_syntax_to__format___main___closed__3;
x_101 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(x_98, x_100);
x_102 = 0;
x_103 = l_lean_parser_syntax_to__format___main___closed__4;
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_101);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_102);
x_105 = x_104;
x_106 = l_lean_parser_syntax_to__format___main___closed__5;
x_107 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_106);
lean::cnstr_set_scalar(x_107, sizeof(void*)*2, x_102);
x_108 = x_107;
x_109 = l_lean_parser_syntax_to__format___main___closed__6;
x_110 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_108);
x_111 = l_lean_format_group___main(x_110);
if (x_52 == 0)
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_112 = l_lean_parser_syntax_to__format___main___closed__8;
x_113 = lean::box(0);
x_114 = l_lean_name_replace__prefix___main(x_49, x_112, x_113);
x_115 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_114);
x_116 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_111);
lean::cnstr_set_scalar(x_116, sizeof(void*)*2, x_102);
x_117 = x_116;
x_118 = lean::cnstr_get(x_44, 1);
lean::inc(x_118);
lean::dec(x_44);
x_121 = l_lean_parser_syntax_to__format__lst___main(x_118);
if (lean::is_scalar(x_99)) {
 x_122 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_122 = x_99;
}
lean::cnstr_set(x_122, 0, x_117);
lean::cnstr_set(x_122, 1, x_121);
x_123 = lean::box(1);
x_124 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_122, x_123);
x_125 = l_lean_format_paren___closed__1;
x_126 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_124);
lean::cnstr_set_scalar(x_126, sizeof(void*)*2, x_102);
x_127 = x_126;
x_128 = l_lean_format_paren___closed__2;
x_129 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_128);
lean::cnstr_set_scalar(x_129, sizeof(void*)*2, x_102);
x_130 = x_129;
x_131 = l_lean_format_paren___closed__3;
x_132 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_130);
x_133 = l_lean_format_group___main(x_132);
return x_133;
}
else
{
obj* x_136; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_49);
lean::dec(x_99);
x_136 = lean::cnstr_get(x_44, 1);
lean::inc(x_136);
lean::dec(x_44);
x_139 = l_lean_parser_syntax_to__format__lst___main(x_136);
x_140 = lean::box(1);
x_141 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_139, x_140);
x_142 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_142, 0, x_111);
lean::cnstr_set(x_142, 1, x_141);
lean::cnstr_set_scalar(x_142, sizeof(void*)*2, x_102);
x_143 = x_142;
x_144 = l_lean_format_sbracket___closed__1;
x_145 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_143);
lean::cnstr_set_scalar(x_145, sizeof(void*)*2, x_102);
x_146 = x_145;
x_147 = l_lean_format_sbracket___closed__2;
x_148 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_148, 0, x_146);
lean::cnstr_set(x_148, 1, x_147);
lean::cnstr_set_scalar(x_148, sizeof(void*)*2, x_102);
x_149 = x_148;
x_150 = l_lean_format_sbracket___closed__3;
x_151 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_151, 0, x_150);
lean::cnstr_set(x_151, 1, x_149);
x_152 = l_lean_format_group___main(x_151);
return x_152;
}
}
}
default:
{
obj* x_153; 
x_153 = l_lean_parser_syntax_to__format___main___closed__9;
return x_153;
}
}
}
}
obj* l_lean_parser_syntax_to__format__lst___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_lean_parser_syntax_to__format___main(x_2);
x_8 = l_lean_parser_syntax_to__format__lst___main(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_to__format(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_to__format___main(x_0);
return x_1;
}
}
obj* l_lean_parser_syntax_to__format__lst(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_to__format__lst___main(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_lean_has__to__format() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_to__format), 1, 0);
return x_0;
}
}
obj* l_lean_to__fmt___at_lean_parser_syntax_has__to__string___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_to__format___main(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_syntax_has__to__string() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_has__repr___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_to__fmt___at_lean_parser_syntax_has__to__string___spec__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
void initialize_init_lean_name();
void initialize_init_lean_parser_parsec();
static bool _G_initialized = false;
void initialize_init_lean_parser_syntax() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_name();
 initialize_init_lean_parser_parsec();
 l_lean_parser_choice = _init_l_lean_parser_choice();
lean::mark_persistent(l_lean_parser_choice);
 l_lean_parser_no__kind = _init_l_lean_parser_no__kind();
lean::mark_persistent(l_lean_parser_no__kind);
 l_lean_parser_macro__scope_decidable__eq = _init_l_lean_parser_macro__scope_decidable__eq();
lean::mark_persistent(l_lean_parser_macro__scope_decidable__eq);
 l_lean_parser_macro__scope_lean_has__to__format = _init_l_lean_parser_macro__scope_lean_has__to__format();
lean::mark_persistent(l_lean_parser_macro__scope_lean_has__to__format);
 l_lean_parser_macro__scope = _init_l_lean_parser_macro__scope();
lean::mark_persistent(l_lean_parser_macro__scope);
 l_lean_parser_macro__scopes = _init_l_lean_parser_macro__scopes();
lean::mark_persistent(l_lean_parser_macro__scopes);
 l_lean_parser_inhabited = _init_l_lean_parser_inhabited();
lean::mark_persistent(l_lean_parser_inhabited);
 l_lean_parser_substring_has__to__string = _init_l_lean_parser_substring_has__to__string();
lean::mark_persistent(l_lean_parser_substring_has__to__string);
 l_lean_parser_syntax_update__leading___closed__1 = _init_l_lean_parser_syntax_update__leading___closed__1();
lean::mark_persistent(l_lean_parser_syntax_update__leading___closed__1);
 l_lean_parser_syntax_reprint___main___closed__1 = _init_l_lean_parser_syntax_reprint___main___closed__1();
lean::mark_persistent(l_lean_parser_syntax_reprint___main___closed__1);
 l_lean_parser_syntax_reprint__lst___main___closed__1 = _init_l_lean_parser_syntax_reprint__lst___main___closed__1();
lean::mark_persistent(l_lean_parser_syntax_reprint__lst___main___closed__1);
 l_lean_parser_syntax_to__format___main___closed__1 = _init_l_lean_parser_syntax_to__format___main___closed__1();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__1);
 l_lean_parser_syntax_to__format___main___closed__2 = _init_l_lean_parser_syntax_to__format___main___closed__2();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__2);
 l_lean_parser_syntax_to__format___main___closed__3 = _init_l_lean_parser_syntax_to__format___main___closed__3();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__3);
 l_lean_parser_syntax_to__format___main___closed__4 = _init_l_lean_parser_syntax_to__format___main___closed__4();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__4);
 l_lean_parser_syntax_to__format___main___closed__5 = _init_l_lean_parser_syntax_to__format___main___closed__5();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__5);
 l_lean_parser_syntax_to__format___main___closed__6 = _init_l_lean_parser_syntax_to__format___main___closed__6();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__6);
 l_lean_parser_syntax_to__format___main___closed__7 = _init_l_lean_parser_syntax_to__format___main___closed__7();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__7);
 l_lean_parser_syntax_to__format___main___closed__8 = _init_l_lean_parser_syntax_to__format___main___closed__8();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__8);
 l_lean_parser_syntax_to__format___main___closed__9 = _init_l_lean_parser_syntax_to__format___main___closed__9();
lean::mark_persistent(l_lean_parser_syntax_to__format___main___closed__9);
 l_lean_parser_syntax_lean_has__to__format = _init_l_lean_parser_syntax_lean_has__to__format();
lean::mark_persistent(l_lean_parser_syntax_lean_has__to__format);
 l_lean_parser_syntax_has__to__string = _init_l_lean_parser_syntax_has__to__string();
lean::mark_persistent(l_lean_parser_syntax_has__to__string);
}

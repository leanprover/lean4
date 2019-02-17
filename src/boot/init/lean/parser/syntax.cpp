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
obj* l_lean_parser_syntax_is__of__kind___boxed(obj*, obj*);
obj* l_list_map___main___at_lean_parser_syntax_to__format___main___spec__3(obj*);
obj* l_list_map___main___at_lean_parser_syntax_to__format___main___spec__5(obj*);
extern obj* l_lean_format_paren___closed__1;
obj* l_lean_parser_macro__scope;
obj* l_lean_parser_syntax_as__node(obj*);
obj* l_lean_parser_syntax_mreplace___main___rarg___lambda__2(obj*, obj*, obj*);
obj* l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__4;
extern obj* l_lean_parser_monad__parsec_sep__by1___rarg___closed__1;
obj* l_lean_parser_macro__scope_decidable__eq;
obj* l_lean_parser_syntax_reprint(obj*);
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
obj* l_lean_parser_syntax_reprint___main___closed__2;
obj* l_lean_parser_macro__scopes;
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
obj* l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_syntax_update__leading(obj*, obj*);
obj* l_lean_parser_syntax_to__format__lst___main(obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_substring_has__to__string;
obj* l_lean_parser_syntax_reprint___main(obj*);
obj* l_lean_parser_syntax_mreplace__lst___main___rarg(obj*, obj*, obj*);
obj* l_lean_parser_syntax_mreplace___main(obj*);
obj* l_lean_parser_syntax_reprint__lst___main(obj*);
obj* l_lean_parser_syntax_kind(obj*);
obj* l_lean_parser_syntax_lean_has__to__format;
obj* l_lean_format_group___main(obj*);
obj* l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(obj*, obj*);
extern obj* l_lean_format_paren___closed__3;
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_string_join(obj*);
obj* l_lean_parser_syntax_mreplace__lst___rarg(obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_syntax_kind___main(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_to__fmt___at_lean_parser_syntax_has__to__string___spec__1(obj*);
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
obj* l___private_init_lean_parser_syntax_1__update__leading__aux(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_list_append___rarg(obj*, obj*);
obj* l___private_init_lean_parser_syntax_1__update__leading__aux___main(obj*, obj*);
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_syntax_mreplace___rarg(obj*, obj*, obj*);
obj* l_lean_parser_syntax_to__format___main___closed__3;
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_syntax_get__head__info___main(obj*);
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
obj* x_1; obj* x_3; obj* x_6; obj* x_9; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::string_iterator_extract(x_1, x_3);
lean::dec(x_3);
lean::dec(x_1);
x_9 = l_string_join___closed__1;
lean::inc(x_9);
x_11 = l_option_get__or__else___main___rarg(x_6, x_9);
return x_11;
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_substring_to__string), 1, 0);
return x_0;
}
}
obj* l_lean_parser_macro__scopes_flip___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_6 = x_1;
}
x_7 = l_lean_parser_macro__scopes_flip___main(x_0, x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; uint8 x_13; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
x_13 = lean::nat_dec_eq(x_2, x_9);
lean::dec(x_9);
if (x_13 == 0)
{
obj* x_16; 
lean::dec(x_11);
if (lean::is_scalar(x_6)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_6;
}
lean::cnstr_set(x_16, 0, x_2);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
else
{
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_2);
return x_11;
}
}
}
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
obj* l_lean_parser_syntax_flip__scopes___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_4 = x_1;
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
x_17 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_17, 0, x_5);
lean::cnstr_set(x_17, 1, x_7);
lean::cnstr_set(x_17, 2, x_9);
lean::cnstr_set(x_17, 3, x_11);
lean::cnstr_set(x_17, 4, x_16);
if (lean::is_scalar(x_4)) {
 x_18 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_18 = x_4;
}
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
case 2:
{
obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_21 = x_1;
}
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_19, 2);
lean::inc(x_26);
lean::dec(x_19);
x_29 = l_lean_parser_macro__scopes_flip___main(x_26, x_0);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_22);
lean::cnstr_set(x_30, 1, x_24);
lean::cnstr_set(x_30, 2, x_29);
if (lean::is_scalar(x_21)) {
 x_31 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_31 = x_21;
}
lean::cnstr_set(x_31, 0, x_30);
return x_31;
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
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
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
obj* x_1; obj* x_3; 
x_1 = l_lean_parser_no__kind;
lean::inc(x_1);
x_3 = l_lean_parser_syntax_mk__node(x_1, x_0);
return x_3;
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
obj* x_2; obj* x_5; uint8 x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean_name_dec_eq(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
if (x_8 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
case 3:
{
uint8 x_14; 
lean::dec(x_0);
x_14 = 0;
return x_14;
}
default:
{
uint8 x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = 0;
return x_17;
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
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__1), 3, 2);
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg), 3, 0);
return x_2;
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
obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
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
lean::inc(x_29);
x_31 = lean::apply_4(x_23, lean::box(0), lean::box(0), x_29, x_28);
x_32 = l_lean_parser_syntax_mreplace__lst___main___rarg(x_0, x_1, x_13);
x_33 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_31, x_32);
return x_33;
}
}
}
obj* l_lean_parser_syntax_mreplace__lst___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace__lst___main___rarg), 3, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___rarg), 3, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace__lst___rarg), 3, 0);
return x_2;
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
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
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
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::inc(x_0);
x_5 = lean::apply_1(x_0, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(x_0, x_6);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_8);
lean::cnstr_set(x_14, 2, x_11);
x_15 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_18; 
lean::dec(x_2);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
return x_18;
}
}
case 3:
{
obj* x_21; obj* x_22; 
x_21 = lean::apply_1(x_0, x_1);
x_22 = l_option_get__or__else___main___rarg(x_21, x_1);
return x_22;
}
default:
{
obj* x_24; obj* x_25; 
lean::inc(x_1);
x_24 = lean::apply_1(x_0, x_1);
x_25 = l_option_get__or__else___main___rarg(x_24, x_1);
return x_25;
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
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_7);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_17 = x_5;
}
x_18 = lean::cnstr_get(x_15, 2);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
lean::dec(x_15);
x_25 = lean::string_iterator_offset(x_1);
x_26 = lean::nat_sub(x_22, x_25);
lean::dec(x_25);
lean::inc(x_1);
x_29 = l_string_iterator_nextn___main(x_1, x_26);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
lean::cnstr_set(x_31, 2, x_18);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_9)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_9;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_7);
if (lean::is_scalar(x_4)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_4;
}
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_20);
return x_36;
}
}
case 1:
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_50; 
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_39 = x_0;
}
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_37, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_37, 3);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_37, 4);
lean::inc(x_48);
if (lean::is_shared(x_37)) {
 lean::dec(x_37);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_37, 0);
 lean::cnstr_release(x_37, 1);
 lean::cnstr_release(x_37, 2);
 lean::cnstr_release(x_37, 3);
 lean::cnstr_release(x_37, 4);
 x_50 = x_37;
}
if (lean::obj_tag(x_40) == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_39);
lean::dec(x_44);
lean::dec(x_42);
lean::dec(x_46);
lean::dec(x_48);
lean::dec(x_50);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_1);
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_59 = lean::cnstr_get(x_40, 0);
lean::inc(x_59);
if (lean::is_shared(x_40)) {
 lean::dec(x_40);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_40, 0);
 x_61 = x_40;
}
x_62 = lean::cnstr_get(x_59, 2);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_62, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_59, 1);
lean::inc(x_66);
lean::dec(x_59);
x_69 = lean::string_iterator_offset(x_1);
x_70 = lean::nat_sub(x_66, x_69);
lean::dec(x_69);
lean::inc(x_1);
x_73 = l_string_iterator_nextn___main(x_1, x_70);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_1);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_66);
lean::cnstr_set(x_75, 2, x_62);
if (lean::is_scalar(x_61)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_61;
}
lean::cnstr_set(x_76, 0, x_75);
if (lean::is_scalar(x_50)) {
 x_77 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_77 = x_50;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_42);
lean::cnstr_set(x_77, 2, x_44);
lean::cnstr_set(x_77, 3, x_46);
lean::cnstr_set(x_77, 4, x_48);
if (lean::is_scalar(x_39)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_39;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_64);
return x_80;
}
}
case 2:
{
obj* x_82; obj* x_83; 
lean::dec(x_0);
x_82 = lean::box(0);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_1);
return x_83;
}
default:
{
obj* x_84; obj* x_85; 
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_1);
return x_85;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_23; obj* x_24; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
lean::inc(x_0);
x_11 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(x_0, x_5, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(x_0, x_7, x_14);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
if (lean::is_scalar(x_9)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_9;
}
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_18);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_16;
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
obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::inc(x_0);
x_8 = lean::apply_2(x_0, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
x_14 = lean::cnstr_get(x_5, 1);
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(x_0, x_14, x_11);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_5, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_5, 2);
lean::inc(x_24);
lean::dec(x_5);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_22);
lean::cnstr_set(x_27, 1, x_17);
lean::cnstr_set(x_27, 2, x_24);
x_28 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
if (lean::is_scalar(x_13)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_13;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_19);
return x_29;
}
else
{
obj* x_32; obj* x_35; 
lean::dec(x_5);
lean::dec(x_0);
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
lean::dec(x_9);
if (lean::is_scalar(x_13)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_13;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_11);
return x_35;
}
}
default:
{
obj* x_36; 
x_36 = lean::box(0);
x_3 = x_36;
goto lbl_4;
}
}
lbl_4:
{
obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_3);
lean::inc(x_1);
x_39 = lean::apply_2(x_0, x_1, x_2);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 lean::cnstr_release(x_39, 1);
 x_44 = x_39;
}
x_45 = l_option_get__or__else___main___rarg(x_40, x_1);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
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
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_mk_iterator(x_0);
x_3 = l_lean_parser_syntax_update__leading___closed__1;
lean::inc(x_3);
x_5 = l_lean_parser_syntax_mreplace___main___at_lean_parser_syntax_update__leading___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_parser_syntax_get__head__info___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_1; obj* x_4; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_parser_syntax_get__head__info__lst___main(x_4);
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
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
return x_12;
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
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l_lean_parser_syntax_get__head__info___main(x_2);
x_8 = l_lean_parser_syntax_get__head__info__lst___main(x_4);
x_9 = l_option_orelse___main___rarg(x_7, x_8);
return x_9;
}
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
obj* l_lean_parser_syntax_get__head__info__lst(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_get__head__info__lst___main(x_0);
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
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
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
obj* l_lean_parser_syntax_reprint__atom___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
return x_3;
}
else
{
obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = l_lean_parser_substring_to__string(x_9);
x_12 = lean::string_append(x_11, x_3);
lean::dec(x_3);
x_14 = lean::cnstr_get(x_6, 2);
lean::inc(x_14);
lean::dec(x_6);
x_17 = l_lean_parser_substring_to__string(x_14);
x_18 = lean::string_append(x_12, x_17);
lean::dec(x_17);
return x_18;
}
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
obj* l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; uint8 x_10; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::string_dec_eq(x_5, x_0);
lean::dec(x_5);
if (x_10 == 0)
{
uint8 x_14; obj* x_15; 
lean::dec(x_7);
lean::dec(x_0);
x_14 = 0;
x_15 = lean::box(x_14);
return x_15;
}
else
{
x_1 = x_7;
goto _start;
}
}
}
}
obj* _init_l_lean_parser_syntax_reprint___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_join), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_syntax_reprint___main___closed__2() {
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
obj* x_1; obj* x_4; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; 
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
}
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = l_lean_parser_substring_to__string(x_13);
x_16 = lean::string_append(x_15, x_6);
lean::dec(x_6);
x_18 = lean::cnstr_get(x_10, 2);
lean::inc(x_18);
lean::dec(x_10);
x_21 = l_lean_parser_substring_to__string(x_18);
x_22 = lean::string_append(x_16, x_21);
lean::dec(x_21);
if (lean::is_scalar(x_12)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_12;
}
lean::cnstr_set(x_24, 0, x_22);
return x_24;
}
}
case 1:
{
obj* x_25; obj* x_28; obj* x_30; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_34; 
x_33 = l_lean_parser_substring_to__string(x_30);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_50; 
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_37 = x_28;
}
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = l_lean_parser_substring_to__string(x_38);
x_41 = l_lean_parser_substring_to__string(x_30);
x_42 = lean::string_append(x_40, x_41);
lean::dec(x_41);
x_44 = lean::cnstr_get(x_35, 2);
lean::inc(x_44);
lean::dec(x_35);
x_47 = l_lean_parser_substring_to__string(x_44);
x_48 = lean::string_append(x_42, x_47);
lean::dec(x_47);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_37;
}
lean::cnstr_set(x_50, 0, x_48);
return x_50;
}
}
case 2:
{
obj* x_51; obj* x_54; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_0, 0);
lean::inc(x_51);
lean::dec(x_0);
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
x_56 = l_lean_parser_choice;
x_57 = lean_name_dec_eq(x_54, x_56);
lean::dec(x_54);
if (x_57 == 0)
{
obj* x_59; obj* x_62; obj* x_63; obj* x_65; 
x_59 = lean::cnstr_get(x_51, 1);
lean::inc(x_59);
lean::dec(x_51);
x_62 = l_lean_parser_syntax_reprint__lst___main(x_59);
x_63 = l_lean_parser_syntax_reprint___main___closed__1;
lean::inc(x_63);
x_65 = l_option_map___rarg(x_63, x_62);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_51, 1);
lean::inc(x_66);
lean::dec(x_51);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; 
x_69 = lean::box(0);
return x_69;
}
else
{
obj* x_70; obj* x_72; obj* x_75; 
x_70 = lean::cnstr_get(x_66, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_66, 1);
lean::inc(x_72);
lean::dec(x_66);
x_75 = l_lean_parser_syntax_reprint___main(x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_77; 
lean::dec(x_72);
x_77 = lean::box(0);
return x_77;
}
else
{
obj* x_78; obj* x_80; obj* x_81; 
x_78 = lean::cnstr_get(x_75, 0);
lean::inc(x_78);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_80 = x_75;
}
x_81 = l_lean_parser_syntax_reprint__lst___main(x_72);
if (lean::obj_tag(x_81) == 0)
{
obj* x_84; 
lean::dec(x_78);
lean::dec(x_80);
x_84 = lean::box(0);
return x_84;
}
else
{
obj* x_85; obj* x_89; uint8 x_90; 
x_85 = lean::cnstr_get(x_81, 0);
lean::inc(x_85);
lean::dec(x_81);
lean::inc(x_78);
x_89 = l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(x_78, x_85);
x_90 = lean::unbox(x_89);
lean::dec(x_89);
if (x_90 == 0)
{
obj* x_94; 
lean::dec(x_78);
lean::dec(x_80);
x_94 = lean::box(0);
return x_94;
}
else
{
obj* x_95; 
if (lean::is_scalar(x_80)) {
 x_95 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_95 = x_80;
}
lean::cnstr_set(x_95, 0, x_78);
return x_95;
}
}
}
}
}
}
default:
{
obj* x_96; 
x_96 = l_lean_parser_syntax_reprint___main___closed__2;
lean::inc(x_96);
return x_96;
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
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_lean_parser_syntax_reprint___main(x_3);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; 
lean::dec(x_7);
lean::dec(x_5);
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_14 = x_8;
}
x_15 = l_lean_parser_syntax_reprint__lst___main(x_5);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; 
lean::dec(x_12);
lean::dec(x_7);
lean::dec(x_14);
x_19 = lean::box(0);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
lean::dec(x_15);
if (lean::is_scalar(x_7)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_7;
}
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_20);
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
}
}
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
obj* x_1; obj* x_3; obj* x_4; 
x_1 = l_lean_name_to__string___closed__1;
lean::inc(x_1);
x_3 = l_lean_name_to__string__with__sep___main(x_1, x_0);
x_4 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
x_14 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_6, x_1);
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
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_1);
x_10 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_4);
return x_10;
}
else
{
obj* x_11; uint8 x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_4);
x_12 = 0;
lean::inc(x_1);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(x_6, x_1);
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
obj* x_9; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_23; uint8 x_24; obj* x_25; obj* x_27; obj* x_28; 
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
lean::inc(x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_24);
x_28 = x_27;
if (lean::obj_tag(x_19) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
x_29 = l_lean_parser_syntax_to__format___main___closed__2;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_24);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_33 = l_lean_parser_syntax_to__format___main___closed__3;
lean::inc(x_33);
x_35 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_19, x_33);
x_36 = l_lean_parser_syntax_to__format___main___closed__4;
lean::inc(x_36);
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_35);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_24);
x_39 = x_38;
x_40 = l_lean_parser_syntax_to__format___main___closed__5;
lean::inc(x_40);
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_24);
x_43 = x_42;
x_44 = l_lean_parser_syntax_to__format___main___closed__6;
lean::inc(x_44);
x_46 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_43);
x_47 = l_lean_format_group___main(x_46);
x_48 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_48, 0, x_28);
lean::cnstr_set(x_48, 1, x_47);
lean::cnstr_set_scalar(x_48, sizeof(void*)*2, x_24);
x_49 = x_48;
return x_49;
}
}
case 2:
{
obj* x_50; obj* x_53; obj* x_55; obj* x_57; uint8 x_58; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
lean::dec(x_0);
x_53 = lean::cnstr_get(x_50, 2);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
x_57 = l_lean_parser_syntax_to__format___main___closed__7;
x_58 = lean_name_dec_eq(x_55, x_57);
if (lean::obj_tag(x_53) == 0)
{
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; 
x_59 = l_lean_parser_syntax_to__format___main___closed__8;
x_60 = lean::box(0);
lean::inc(x_59);
x_62 = l_lean_name_replace__prefix___main(x_55, x_59, x_60);
x_63 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_62);
x_64 = 0;
x_65 = l_lean_parser_syntax_to__format___main___closed__2;
lean::inc(x_65);
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set(x_67, 1, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_64);
x_68 = x_67;
x_69 = lean::cnstr_get(x_50, 1);
lean::inc(x_69);
lean::dec(x_50);
x_72 = l_lean_parser_syntax_to__format__lst___main(x_69);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_68);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::box(1);
x_75 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_73, x_74);
x_76 = l_lean_format_paren___closed__1;
lean::inc(x_76);
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_75);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_64);
x_79 = x_78;
x_80 = l_lean_format_paren___closed__2;
lean::inc(x_80);
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_79);
lean::cnstr_set(x_82, 1, x_80);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_64);
x_83 = x_82;
x_84 = l_lean_format_paren___closed__3;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_83);
x_87 = l_lean_format_group___main(x_86);
return x_87;
}
else
{
obj* x_89; obj* x_92; obj* x_93; obj* x_94; uint8 x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_110; obj* x_111; 
lean::dec(x_55);
x_89 = lean::cnstr_get(x_50, 1);
lean::inc(x_89);
lean::dec(x_50);
x_92 = l_lean_parser_syntax_to__format__lst___main(x_89);
x_93 = lean::box(1);
x_94 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_92, x_93);
x_95 = 0;
x_96 = l_lean_parser_syntax_to__format___main___closed__2;
lean::inc(x_96);
x_98 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set(x_98, 1, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*2, x_95);
x_99 = x_98;
x_100 = l_lean_format_sbracket___closed__1;
lean::inc(x_100);
x_102 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_99);
lean::cnstr_set_scalar(x_102, sizeof(void*)*2, x_95);
x_103 = x_102;
x_104 = l_lean_format_sbracket___closed__2;
lean::inc(x_104);
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_104);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_95);
x_107 = x_106;
x_108 = l_lean_format_sbracket___closed__3;
lean::inc(x_108);
x_110 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set(x_110, 1, x_107);
x_111 = l_lean_format_group___main(x_110);
return x_111;
}
}
else
{
obj* x_112; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_119; obj* x_120; obj* x_121; obj* x_123; obj* x_124; obj* x_125; obj* x_127; obj* x_128; 
x_112 = l_list_reverse___rarg(x_53);
x_113 = l_lean_parser_syntax_to__format___main___closed__3;
lean::inc(x_113);
x_115 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(x_112, x_113);
x_116 = 0;
x_117 = l_lean_parser_syntax_to__format___main___closed__4;
lean::inc(x_117);
x_119 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_119, 0, x_117);
lean::cnstr_set(x_119, 1, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*2, x_116);
x_120 = x_119;
x_121 = l_lean_parser_syntax_to__format___main___closed__5;
lean::inc(x_121);
x_123 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_123, 0, x_120);
lean::cnstr_set(x_123, 1, x_121);
lean::cnstr_set_scalar(x_123, sizeof(void*)*2, x_116);
x_124 = x_123;
x_125 = l_lean_parser_syntax_to__format___main___closed__6;
lean::inc(x_125);
x_127 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_127, 0, x_125);
lean::cnstr_set(x_127, 1, x_124);
x_128 = l_lean_format_group___main(x_127);
if (x_58 == 0)
{
obj* x_129; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_149; obj* x_150; obj* x_151; obj* x_153; obj* x_154; 
x_129 = l_lean_parser_syntax_to__format___main___closed__8;
x_130 = lean::box(0);
lean::inc(x_129);
x_132 = l_lean_name_replace__prefix___main(x_55, x_129, x_130);
x_133 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_132);
x_134 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_128);
lean::cnstr_set_scalar(x_134, sizeof(void*)*2, x_116);
x_135 = x_134;
x_136 = lean::cnstr_get(x_50, 1);
lean::inc(x_136);
lean::dec(x_50);
x_139 = l_lean_parser_syntax_to__format__lst___main(x_136);
x_140 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_140, 0, x_135);
lean::cnstr_set(x_140, 1, x_139);
x_141 = lean::box(1);
x_142 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_140, x_141);
x_143 = l_lean_format_paren___closed__1;
lean::inc(x_143);
x_145 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_142);
lean::cnstr_set_scalar(x_145, sizeof(void*)*2, x_116);
x_146 = x_145;
x_147 = l_lean_format_paren___closed__2;
lean::inc(x_147);
x_149 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_149, 0, x_146);
lean::cnstr_set(x_149, 1, x_147);
lean::cnstr_set_scalar(x_149, sizeof(void*)*2, x_116);
x_150 = x_149;
x_151 = l_lean_format_paren___closed__3;
lean::inc(x_151);
x_153 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_153, 0, x_151);
lean::cnstr_set(x_153, 1, x_150);
x_154 = l_lean_format_group___main(x_153);
return x_154;
}
else
{
obj* x_156; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_166; obj* x_167; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_174; obj* x_175; 
lean::dec(x_55);
x_156 = lean::cnstr_get(x_50, 1);
lean::inc(x_156);
lean::dec(x_50);
x_159 = l_lean_parser_syntax_to__format__lst___main(x_156);
x_160 = lean::box(1);
x_161 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_159, x_160);
x_162 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_162, 0, x_128);
lean::cnstr_set(x_162, 1, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*2, x_116);
x_163 = x_162;
x_164 = l_lean_format_sbracket___closed__1;
lean::inc(x_164);
x_166 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_166, 0, x_164);
lean::cnstr_set(x_166, 1, x_163);
lean::cnstr_set_scalar(x_166, sizeof(void*)*2, x_116);
x_167 = x_166;
x_168 = l_lean_format_sbracket___closed__2;
lean::inc(x_168);
x_170 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_170, 0, x_167);
lean::cnstr_set(x_170, 1, x_168);
lean::cnstr_set_scalar(x_170, sizeof(void*)*2, x_116);
x_171 = x_170;
x_172 = l_lean_format_sbracket___closed__3;
lean::inc(x_172);
x_174 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_174, 0, x_172);
lean::cnstr_set(x_174, 1, x_171);
x_175 = l_lean_format_group___main(x_174);
return x_175;
}
}
}
default:
{
obj* x_176; 
x_176 = l_lean_parser_syntax_to__format___main___closed__9;
lean::inc(x_176);
return x_176;
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
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_6 = x_0;
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
 l_lean_parser_no__kind = _init_l_lean_parser_no__kind();
 l_lean_parser_macro__scope_decidable__eq = _init_l_lean_parser_macro__scope_decidable__eq();
 l_lean_parser_macro__scope_lean_has__to__format = _init_l_lean_parser_macro__scope_lean_has__to__format();
 l_lean_parser_macro__scope = _init_l_lean_parser_macro__scope();
 l_lean_parser_macro__scopes = _init_l_lean_parser_macro__scopes();
 l_lean_parser_inhabited = _init_l_lean_parser_inhabited();
 l_lean_parser_substring_has__to__string = _init_l_lean_parser_substring_has__to__string();
 l_lean_parser_syntax_update__leading___closed__1 = _init_l_lean_parser_syntax_update__leading___closed__1();
 l_lean_parser_syntax_reprint___main___closed__1 = _init_l_lean_parser_syntax_reprint___main___closed__1();
 l_lean_parser_syntax_reprint___main___closed__2 = _init_l_lean_parser_syntax_reprint___main___closed__2();
 l_lean_parser_syntax_reprint__lst___main___closed__1 = _init_l_lean_parser_syntax_reprint__lst___main___closed__1();
 l_lean_parser_syntax_to__format___main___closed__1 = _init_l_lean_parser_syntax_to__format___main___closed__1();
 l_lean_parser_syntax_to__format___main___closed__2 = _init_l_lean_parser_syntax_to__format___main___closed__2();
 l_lean_parser_syntax_to__format___main___closed__3 = _init_l_lean_parser_syntax_to__format___main___closed__3();
 l_lean_parser_syntax_to__format___main___closed__4 = _init_l_lean_parser_syntax_to__format___main___closed__4();
 l_lean_parser_syntax_to__format___main___closed__5 = _init_l_lean_parser_syntax_to__format___main___closed__5();
 l_lean_parser_syntax_to__format___main___closed__6 = _init_l_lean_parser_syntax_to__format___main___closed__6();
 l_lean_parser_syntax_to__format___main___closed__7 = _init_l_lean_parser_syntax_to__format___main___closed__7();
 l_lean_parser_syntax_to__format___main___closed__8 = _init_l_lean_parser_syntax_to__format___main___closed__8();
 l_lean_parser_syntax_to__format___main___closed__9 = _init_l_lean_parser_syntax_to__format___main___closed__9();
 l_lean_parser_syntax_lean_has__to__format = _init_l_lean_parser_syntax_lean_has__to__format();
 l_lean_parser_syntax_has__to__string = _init_l_lean_parser_syntax_has__to__string();
}

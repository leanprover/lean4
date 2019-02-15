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
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_macro__scopes() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_3);
return x_12;
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
case 0:
{
lean::dec(x_0);
return x_1;
}
case 1:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_3, 3);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 4);
lean::inc(x_14);
lean::dec(x_3);
x_17 = l_lean_parser_macro__scopes_flip___main(x_14, x_0);
x_18 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_8);
lean::cnstr_set(x_18, 2, x_10);
lean::cnstr_set(x_18, 3, x_12);
lean::cnstr_set(x_18, 4, x_17);
if (lean::is_scalar(x_5)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_5;
}
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
case 2:
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_22 = x_1;
}
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 2);
lean::inc(x_27);
lean::dec(x_20);
x_30 = l_lean_parser_macro__scopes_flip___main(x_27, x_0);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_23);
lean::cnstr_set(x_31, 1, x_25);
lean::cnstr_set(x_31, 2, x_30);
if (lean::is_scalar(x_22)) {
 x_32 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_32 = x_22;
}
lean::cnstr_set(x_32, 0, x_31);
return x_32;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
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
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
x_12 = l_lean_parser_syntax_flip__scopes___main(x_10, x_5);
x_13 = l_list_map___main___at_lean_parser_syntax_as__node___main___spec__1(x_0, x_7);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* l_lean_parser_syntax_as__node___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 2:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = l_list_map___main___at_lean_parser_syntax_as__node___main___spec__1(x_5, x_10);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
default:
{
obj* x_17; 
lean::dec(x_0);
x_17 = lean::box(0);
return x_17;
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
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 2:
{
obj* x_5; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
default:
{
obj* x_13; 
lean::dec(x_0);
x_13 = lean::box(0);
return x_13;
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
case 0:
{
uint8 x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
return x_4;
}
case 1:
{
uint8 x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = 0;
return x_7;
}
case 2:
{
obj* x_8; obj* x_11; uint8 x_14; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean_name_dec_eq(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
if (x_14 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
default:
{
uint8 x_21; 
lean::dec(x_1);
lean::dec(x_0);
x_21 = 0;
return x_21;
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
obj* l_lean_parser_syntax_mreplace___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_5; 
x_5 = lean::box(0);
x_3 = x_5;
goto lbl_4;
}
case 1:
{
obj* x_6; 
x_6 = lean::box(0);
x_3 = x_6;
goto lbl_4;
}
case 2:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::inc(x_1);
x_12 = lean::apply_1(x_1, x_2);
lean::inc(x_9);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__3), 5, 4);
lean::closure_set(x_14, 0, x_7);
lean::closure_set(x_14, 1, x_0);
lean::closure_set(x_14, 2, x_1);
lean::closure_set(x_14, 3, x_9);
x_15 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_14);
return x_15;
}
default:
{
obj* x_16; 
x_16 = lean::box(0);
x_3 = x_16;
goto lbl_4;
}
}
lbl_4:
{
obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_3);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::inc(x_2);
x_21 = lean::apply_1(x_1, x_2);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_22, 0, x_0);
lean::closure_set(x_22, 1, x_2);
x_23 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_21, x_22);
return x_23;
}
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
obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_1);
x_9 = l_lean_parser_syntax_mreplace__lst___main___rarg(x_1, x_2, x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_syntax_mreplace___main___rarg___lambda__2), 3, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_0);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_4, 0);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_2(x_21, lean::box(0), x_15);
return x_24;
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
case 0:
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = lean::apply_1(x_0, x_1);
x_4 = l_option_get__or__else___main___rarg(x_3, x_1);
return x_4;
}
case 1:
{
obj* x_6; obj* x_7; 
lean::inc(x_1);
x_6 = lean::apply_1(x_0, x_1);
x_7 = l_option_get__or__else___main___rarg(x_6, x_1);
return x_7;
}
case 2:
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_22; 
lean::dec(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_replace___spec__2(x_0, x_13);
x_16 = lean::cnstr_get(x_8, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_8, 2);
lean::inc(x_18);
lean::dec(x_8);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_18);
x_22 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
return x_22;
}
else
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_0);
x_25 = lean::cnstr_get(x_11, 0);
lean::inc(x_25);
lean::dec(x_11);
return x_25;
}
}
default:
{
obj* x_29; obj* x_30; 
lean::inc(x_1);
x_29 = lean::apply_1(x_0, x_1);
x_30 = l_option_get__or__else___main___rarg(x_29, x_1);
return x_30;
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
obj* x_14; obj* x_15; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_4);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_18 = x_5;
}
x_19 = lean::cnstr_get(x_16, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_19, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
lean::dec(x_16);
x_26 = lean::string_iterator_offset(x_1);
x_27 = lean::nat_sub(x_23, x_26);
lean::dec(x_26);
lean::inc(x_1);
x_30 = l_string_iterator_nextn___main(x_1, x_27);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_23);
lean::cnstr_set(x_32, 2, x_19);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_32);
if (lean::is_scalar(x_9)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_9;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_7);
if (lean::is_scalar(x_4)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_4;
}
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_21);
return x_37;
}
}
case 1:
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_49; obj* x_51; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_40 = x_0;
}
x_41 = lean::cnstr_get(x_38, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_38, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_38, 3);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_38, 4);
lean::inc(x_49);
if (lean::is_shared(x_38)) {
 lean::dec(x_38);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 lean::cnstr_release(x_38, 2);
 lean::cnstr_release(x_38, 3);
 lean::cnstr_release(x_38, 4);
 x_51 = x_38;
}
if (lean::obj_tag(x_41) == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_43);
lean::dec(x_49);
lean::dec(x_51);
lean::dec(x_47);
lean::dec(x_41);
lean::dec(x_45);
lean::dec(x_40);
x_59 = lean::box(0);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_1);
return x_60;
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_61 = lean::cnstr_get(x_41, 0);
lean::inc(x_61);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_63 = x_41;
}
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_61, 1);
lean::inc(x_68);
lean::dec(x_61);
x_71 = lean::string_iterator_offset(x_1);
x_72 = lean::nat_sub(x_68, x_71);
lean::dec(x_71);
lean::inc(x_1);
x_75 = l_string_iterator_nextn___main(x_1, x_72);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_1);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_68);
lean::cnstr_set(x_77, 2, x_64);
if (lean::is_scalar(x_63)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_63;
}
lean::cnstr_set(x_78, 0, x_77);
if (lean::is_scalar(x_51)) {
 x_79 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_79 = x_51;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_43);
lean::cnstr_set(x_79, 2, x_45);
lean::cnstr_set(x_79, 3, x_47);
lean::cnstr_set(x_79, 4, x_49);
if (lean::is_scalar(x_40)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_40;
}
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_66);
return x_82;
}
}
case 2:
{
obj* x_84; obj* x_85; 
lean::dec(x_0);
x_84 = lean::box(0);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_1);
return x_85;
}
default:
{
obj* x_87; obj* x_88; 
lean::dec(x_0);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_1);
return x_88;
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
case 0:
{
obj* x_5; 
x_5 = lean::box(0);
x_3 = x_5;
goto lbl_4;
}
case 1:
{
obj* x_6; 
x_6 = lean::box(0);
x_3 = x_6;
goto lbl_4;
}
case 2:
{
obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::inc(x_0);
x_10 = lean::apply_2(x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_11);
x_17 = lean::cnstr_get(x_7, 1);
lean::inc(x_17);
x_19 = l_lean_parser_syntax_mreplace__lst___main___at_lean_parser_syntax_update__leading___spec__2(x_0, x_17, x_13);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_7, 2);
lean::inc(x_27);
lean::dec(x_7);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_20);
lean::cnstr_set(x_30, 2, x_27);
x_31 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_22);
return x_32;
}
else
{
obj* x_35; obj* x_38; 
lean::dec(x_7);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_11, 0);
lean::inc(x_35);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_15;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_13);
return x_38;
}
}
default:
{
obj* x_39; 
x_39 = lean::box(0);
x_3 = x_39;
goto lbl_4;
}
}
lbl_4:
{
obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_3);
lean::inc(x_1);
x_42 = lean::apply_2(x_0, x_1, x_2);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_47 = x_42;
}
x_48 = l_option_get__or__else___main___rarg(x_43, x_1);
if (lean::is_scalar(x_47)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_47;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_45);
return x_49;
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
case 0:
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
return x_4;
}
case 1:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
return x_10;
}
case 2:
{
obj* x_13; obj* x_16; obj* x_19; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_lean_parser_syntax_get__head__info__lst___main(x_16);
return x_19;
}
default:
{
obj* x_21; 
lean::dec(x_0);
x_21 = lean::box(0);
return x_21;
}
}
}
}
obj* l_lean_parser_syntax_get__head__info__lst___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_syntax_get__head__info___main(x_3);
x_9 = l_lean_parser_syntax_get__head__info__lst___main(x_5);
x_10 = l_option_orelse___main___rarg(x_8, x_9);
return x_10;
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
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
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
lean::dec(x_1);
return x_3;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = l_lean_parser_substring_to__string(x_10);
x_13 = lean::string_append(x_12, x_3);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_7, 2);
lean::inc(x_15);
lean::dec(x_7);
x_18 = l_lean_parser_substring_to__string(x_15);
x_19 = lean::string_append(x_13, x_18);
lean::dec(x_18);
return x_19;
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
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; uint8 x_11; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::string_dec_eq(x_6, x_0);
lean::dec(x_6);
if (x_11 == 0)
{
uint8 x_15; obj* x_16; 
lean::dec(x_8);
lean::dec(x_0);
x_15 = 0;
x_16 = lean::box(x_15);
return x_16;
}
else
{
x_1 = x_8;
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
obj* x_10; 
lean::dec(x_4);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_13 = x_4;
}
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = l_lean_parser_substring_to__string(x_14);
x_17 = lean::string_append(x_16, x_6);
lean::dec(x_6);
x_19 = lean::cnstr_get(x_11, 2);
lean::inc(x_19);
lean::dec(x_11);
x_22 = l_lean_parser_substring_to__string(x_19);
x_23 = lean::string_append(x_17, x_22);
lean::dec(x_22);
if (lean::is_scalar(x_13)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_13;
}
lean::cnstr_set(x_25, 0, x_23);
return x_25;
}
}
case 1:
{
obj* x_26; obj* x_29; obj* x_31; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
lean::dec(x_26);
if (lean::obj_tag(x_29) == 0)
{
obj* x_35; obj* x_36; 
lean::dec(x_29);
x_35 = l_lean_parser_substring_to__string(x_31);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_52; 
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_39 = x_29;
}
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = l_lean_parser_substring_to__string(x_40);
x_43 = l_lean_parser_substring_to__string(x_31);
x_44 = lean::string_append(x_42, x_43);
lean::dec(x_43);
x_46 = lean::cnstr_get(x_37, 2);
lean::inc(x_46);
lean::dec(x_37);
x_49 = l_lean_parser_substring_to__string(x_46);
x_50 = lean::string_append(x_44, x_49);
lean::dec(x_49);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_50);
return x_52;
}
}
case 2:
{
obj* x_53; obj* x_56; obj* x_58; uint8 x_59; 
x_53 = lean::cnstr_get(x_0, 0);
lean::inc(x_53);
lean::dec(x_0);
x_56 = lean::cnstr_get(x_53, 0);
lean::inc(x_56);
x_58 = l_lean_parser_choice;
x_59 = lean_name_dec_eq(x_56, x_58);
lean::dec(x_56);
if (x_59 == 0)
{
obj* x_61; obj* x_64; obj* x_65; obj* x_67; 
x_61 = lean::cnstr_get(x_53, 1);
lean::inc(x_61);
lean::dec(x_53);
x_64 = l_lean_parser_syntax_reprint__lst___main(x_61);
x_65 = l_lean_parser_syntax_reprint___main___closed__1;
lean::inc(x_65);
x_67 = l_option_map___rarg(x_65, x_64);
return x_67;
}
else
{
obj* x_68; 
x_68 = lean::cnstr_get(x_53, 1);
lean::inc(x_68);
lean::dec(x_53);
if (lean::obj_tag(x_68) == 0)
{
obj* x_72; 
lean::dec(x_68);
x_72 = lean::box(0);
return x_72;
}
else
{
obj* x_73; obj* x_75; obj* x_78; 
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_68, 1);
lean::inc(x_75);
lean::dec(x_68);
x_78 = l_lean_parser_syntax_reprint___main(x_73);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; 
lean::dec(x_78);
lean::dec(x_75);
x_81 = lean::box(0);
return x_81;
}
else
{
obj* x_82; obj* x_84; obj* x_85; 
x_82 = lean::cnstr_get(x_78, 0);
lean::inc(x_82);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_84 = x_78;
}
x_85 = l_lean_parser_syntax_reprint__lst___main(x_75);
if (lean::obj_tag(x_85) == 0)
{
obj* x_89; 
lean::dec(x_85);
lean::dec(x_84);
lean::dec(x_82);
x_89 = lean::box(0);
return x_89;
}
else
{
obj* x_90; obj* x_94; uint8 x_95; 
x_90 = lean::cnstr_get(x_85, 0);
lean::inc(x_90);
lean::dec(x_85);
lean::inc(x_82);
x_94 = l_list_foldr___main___at_lean_parser_syntax_reprint___main___spec__1(x_82, x_90);
x_95 = lean::unbox(x_94);
lean::dec(x_94);
if (x_95 == 0)
{
obj* x_99; 
lean::dec(x_84);
lean::dec(x_82);
x_99 = lean::box(0);
return x_99;
}
else
{
obj* x_100; 
if (lean::is_scalar(x_84)) {
 x_100 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_100 = x_84;
}
lean::cnstr_set(x_100, 0, x_82);
return x_100;
}
}
}
}
}
}
default:
{
obj* x_102; 
lean::dec(x_0);
x_102 = l_lean_parser_syntax_reprint___main___closed__2;
lean::inc(x_102);
return x_102;
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
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_parser_syntax_reprint__lst___main___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_8 = x_0;
}
x_9 = l_lean_parser_syntax_reprint___main(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_13; 
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_9);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_16 = x_9;
}
x_17 = l_lean_parser_syntax_reprint__lst___main(x_6);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; 
lean::dec(x_8);
lean::dec(x_16);
lean::dec(x_14);
lean::dec(x_17);
x_22 = lean::box(0);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_17, 0);
lean::inc(x_23);
lean::dec(x_17);
if (lean::is_scalar(x_8)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_8;
}
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_23);
if (lean::is_scalar(x_16)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_16;
}
lean::cnstr_set(x_27, 0, x_26);
return x_27;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_3);
x_9 = l_list_map___main___at_lean_parser_syntax_to__format___main___spec__3(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_3);
x_9 = l_list_map___main___at_lean_parser_syntax_to__format___main___spec__5(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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
x_16 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_7, x_1);
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
obj* l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(obj* x_0, obj* x_1) {
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
obj* x_12; 
lean::dec(x_7);
lean::dec(x_1);
x_12 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_5);
return x_12;
}
else
{
obj* x_13; uint8 x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__4(x_5);
x_14 = 0;
lean::inc(x_1);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_1);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_14);
x_17 = x_16;
x_18 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(x_7, x_1);
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_14);
x_20 = x_19;
return x_20;
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
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_19);
x_30 = l_lean_parser_syntax_to__format___main___closed__2;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_24);
x_33 = x_32;
return x_33;
}
else
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_34 = l_lean_parser_syntax_to__format___main___closed__3;
lean::inc(x_34);
x_36 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_19, x_34);
x_37 = l_lean_parser_syntax_to__format___main___closed__4;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_24);
x_40 = x_39;
x_41 = l_lean_parser_syntax_to__format___main___closed__5;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_24);
x_44 = x_43;
x_45 = l_lean_parser_syntax_to__format___main___closed__6;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_44);
x_48 = l_lean_format_group___main(x_47);
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_28);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_24);
x_50 = x_49;
return x_50;
}
}
case 2:
{
obj* x_51; obj* x_54; obj* x_56; obj* x_58; uint8 x_59; 
x_51 = lean::cnstr_get(x_0, 0);
lean::inc(x_51);
lean::dec(x_0);
x_54 = lean::cnstr_get(x_51, 2);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 0);
lean::inc(x_56);
x_58 = l_lean_parser_syntax_to__format___main___closed__7;
x_59 = lean_name_dec_eq(x_56, x_58);
if (lean::obj_tag(x_54) == 0)
{
lean::dec(x_54);
if (x_59 == 0)
{
obj* x_61; obj* x_62; obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_88; obj* x_89; 
x_61 = l_lean_parser_syntax_to__format___main___closed__8;
x_62 = lean::box(0);
lean::inc(x_61);
x_64 = l_lean_name_replace__prefix___main(x_56, x_61, x_62);
x_65 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_64);
x_66 = 0;
x_67 = l_lean_parser_syntax_to__format___main___closed__2;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_66);
x_70 = x_69;
x_71 = lean::cnstr_get(x_51, 1);
lean::inc(x_71);
lean::dec(x_51);
x_74 = l_lean_parser_syntax_to__format__lst___main(x_71);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_70);
lean::cnstr_set(x_75, 1, x_74);
x_76 = lean::box(1);
x_77 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_75, x_76);
x_78 = l_lean_format_paren___closed__1;
lean::inc(x_78);
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_77);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_66);
x_81 = x_80;
x_82 = l_lean_format_paren___closed__2;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_82);
lean::cnstr_set_scalar(x_84, sizeof(void*)*2, x_66);
x_85 = x_84;
x_86 = l_lean_format_paren___closed__3;
lean::inc(x_86);
x_88 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_85);
x_89 = l_lean_format_group___main(x_88);
return x_89;
}
else
{
obj* x_91; obj* x_94; obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_108; obj* x_109; obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_56);
x_91 = lean::cnstr_get(x_51, 1);
lean::inc(x_91);
lean::dec(x_51);
x_94 = l_lean_parser_syntax_to__format__lst___main(x_91);
x_95 = lean::box(1);
x_96 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_94, x_95);
x_97 = 0;
x_98 = l_lean_parser_syntax_to__format___main___closed__2;
lean::inc(x_98);
x_100 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set(x_100, 1, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*2, x_97);
x_101 = x_100;
x_102 = l_lean_format_sbracket___closed__1;
lean::inc(x_102);
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set(x_104, 1, x_101);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_97);
x_105 = x_104;
x_106 = l_lean_format_sbracket___closed__2;
lean::inc(x_106);
x_108 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_108, 0, x_105);
lean::cnstr_set(x_108, 1, x_106);
lean::cnstr_set_scalar(x_108, sizeof(void*)*2, x_97);
x_109 = x_108;
x_110 = l_lean_format_sbracket___closed__3;
lean::inc(x_110);
x_112 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_109);
x_113 = l_lean_format_group___main(x_112);
return x_113;
}
}
else
{
obj* x_114; obj* x_115; obj* x_117; uint8 x_118; obj* x_119; obj* x_121; obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_129; obj* x_130; 
x_114 = l_list_reverse___rarg(x_54);
x_115 = l_lean_parser_syntax_to__format___main___closed__3;
lean::inc(x_115);
x_117 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__8(x_114, x_115);
x_118 = 0;
x_119 = l_lean_parser_syntax_to__format___main___closed__4;
lean::inc(x_119);
x_121 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_117);
lean::cnstr_set_scalar(x_121, sizeof(void*)*2, x_118);
x_122 = x_121;
x_123 = l_lean_parser_syntax_to__format___main___closed__5;
lean::inc(x_123);
x_125 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_125, 0, x_122);
lean::cnstr_set(x_125, 1, x_123);
lean::cnstr_set_scalar(x_125, sizeof(void*)*2, x_118);
x_126 = x_125;
x_127 = l_lean_parser_syntax_to__format___main___closed__6;
lean::inc(x_127);
x_129 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_126);
x_130 = l_lean_format_group___main(x_129);
if (x_59 == 0)
{
obj* x_131; obj* x_132; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_147; obj* x_148; obj* x_149; obj* x_151; obj* x_152; obj* x_153; obj* x_155; obj* x_156; 
x_131 = l_lean_parser_syntax_to__format___main___closed__8;
x_132 = lean::box(0);
lean::inc(x_131);
x_134 = l_lean_name_replace__prefix___main(x_56, x_131, x_132);
x_135 = l_lean_to__fmt___at_lean_parser_syntax_to__format___main___spec__2(x_134);
x_136 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_130);
lean::cnstr_set_scalar(x_136, sizeof(void*)*2, x_118);
x_137 = x_136;
x_138 = lean::cnstr_get(x_51, 1);
lean::inc(x_138);
lean::dec(x_51);
x_141 = l_lean_parser_syntax_to__format__lst___main(x_138);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_137);
lean::cnstr_set(x_142, 1, x_141);
x_143 = lean::box(1);
x_144 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_142, x_143);
x_145 = l_lean_format_paren___closed__1;
lean::inc(x_145);
x_147 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_144);
lean::cnstr_set_scalar(x_147, sizeof(void*)*2, x_118);
x_148 = x_147;
x_149 = l_lean_format_paren___closed__2;
lean::inc(x_149);
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_148);
lean::cnstr_set(x_151, 1, x_149);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_118);
x_152 = x_151;
x_153 = l_lean_format_paren___closed__3;
lean::inc(x_153);
x_155 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_155, 0, x_153);
lean::cnstr_set(x_155, 1, x_152);
x_156 = l_lean_format_group___main(x_155);
return x_156;
}
else
{
obj* x_158; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_168; obj* x_169; obj* x_170; obj* x_172; obj* x_173; obj* x_174; obj* x_176; obj* x_177; 
lean::dec(x_56);
x_158 = lean::cnstr_get(x_51, 1);
lean::inc(x_158);
lean::dec(x_51);
x_161 = l_lean_parser_syntax_to__format__lst___main(x_158);
x_162 = lean::box(1);
x_163 = l_lean_format_join__sep___main___at_lean_parser_syntax_to__format___main___spec__6(x_161, x_162);
x_164 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_164, 0, x_130);
lean::cnstr_set(x_164, 1, x_163);
lean::cnstr_set_scalar(x_164, sizeof(void*)*2, x_118);
x_165 = x_164;
x_166 = l_lean_format_sbracket___closed__1;
lean::inc(x_166);
x_168 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_165);
lean::cnstr_set_scalar(x_168, sizeof(void*)*2, x_118);
x_169 = x_168;
x_170 = l_lean_format_sbracket___closed__2;
lean::inc(x_170);
x_172 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_172, 0, x_169);
lean::cnstr_set(x_172, 1, x_170);
lean::cnstr_set_scalar(x_172, sizeof(void*)*2, x_118);
x_173 = x_172;
x_174 = l_lean_format_sbracket___closed__3;
lean::inc(x_174);
x_176 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_173);
x_177 = l_lean_format_group___main(x_176);
return x_177;
}
}
}
default:
{
obj* x_179; 
lean::dec(x_0);
x_179 = l_lean_parser_syntax_to__format___main___closed__9;
lean::inc(x_179);
return x_179;
}
}
}
}
obj* l_lean_parser_syntax_to__format__lst___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = l_lean_parser_syntax_to__format___main(x_3);
x_9 = l_lean_parser_syntax_to__format__lst___main(x_5);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
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

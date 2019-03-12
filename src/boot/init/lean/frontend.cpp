// Lean compiler output
// Module: init.lean.frontend
// Imports: init.default init.lean.parser.module init.lean.expander init.lean.elaborator init.lean.util init.io
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
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3___boxed(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_process__file___lambda__1___closed__6;
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3(obj*, obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_parser_parse__command(obj*, obj*);
obj* l_string_quote(obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2;
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_io_println___at_lean_process__file___spec__1___boxed(obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2___boxed(obj*, obj*, obj*);
obj* l_io_print___at_lean_process__file___spec__2___boxed(obj*, obj*);
obj* l_io_println___at_lean_process__file___spec__1(obj*, obj*);
extern obj* l_lean_options_mk;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1;
obj* l_lean_parser_parse__header(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__8;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___closed__1;
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_io_print___at_lean_process__file___spec__2(obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_lean_profileit__pure___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__4;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(obj*, obj*, obj*);
obj* l_lean_mk__config(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = l_lean_parser_module_header_parser_lean_parser_has__tokens;
x_3 = l_lean_parser_tokens___rarg(x_2);
x_4 = l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
x_5 = l_lean_parser_tokens___rarg(x_4);
x_6 = l_list_append___rarg(x_3, x_5);
x_7 = l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
x_8 = l_lean_parser_tokens___rarg(x_7);
x_9 = l_list_append___rarg(x_6, x_8);
x_10 = l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
x_11 = l_lean_parser_tokens___rarg(x_10);
x_12 = l_list_append___rarg(x_9, x_11);
x_13 = l_lean_parser_mk__token__trie(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_18 = x_13;
} else {
 lean::inc(x_16);
 lean::dec(x_13);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
lean::inc(x_1);
x_24 = l_lean_file__map_from__string(x_1);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_20);
x_27 = lean::box(0);
x_28 = l_lean_parser_term_builtin__leading__parsers;
x_29 = l_lean_parser_term_builtin__trailing__parsers;
x_30 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set(x_30, 2, x_29);
lean::cnstr_set(x_30, 3, x_27);
lean::cnstr_set(x_30, 4, x_27);
x_31 = l_lean_parser_command_builtin__command__parsers;
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
if (lean::is_scalar(x_22)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_22;
}
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_1 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_1 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_1 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_1 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__command(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_expand(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_process__command(x_0, x_1, x_2);
return x_4;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_24; obj* x_27; obj* x_29; obj* x_32; obj* x_34; obj* x_37; obj* x_40; obj* x_43; obj* x_45; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_55; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
lean::dec(x_7);
x_21 = lean::cnstr_get(x_12, 0);
lean::inc(x_21);
lean::dec(x_12);
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
lean::dec(x_14);
x_27 = lean::cnstr_get(x_16, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_16, 1);
lean::inc(x_29);
lean::dec(x_16);
x_32 = lean::cnstr_get(x_24, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_32, 0);
lean::inc(x_34);
lean::dec(x_32);
x_37 = lean::cnstr_get(x_34, 0);
lean::inc(x_37);
lean::dec(x_34);
x_40 = lean::cnstr_get(x_37, 2);
lean::inc(x_40);
lean::dec(x_37);
x_43 = lean::cnstr_get(x_18, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_43, 1);
lean::inc(x_45);
lean::dec(x_43);
x_48 = l_lean_file__map_to__position(x_40, x_45);
lean::inc(x_24);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_50, 0, x_24);
lean::closure_set(x_50, 1, x_18);
x_51 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1;
x_52 = l_lean_profileit__pure___rarg(x_51, x_48, x_50, x_8);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_64; obj* x_67; obj* x_71; obj* x_72; 
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_48);
lean::dec(x_27);
x_61 = lean::cnstr_get(x_52, 1);
lean::inc(x_61);
lean::dec(x_52);
x_64 = lean::cnstr_get(x_53, 0);
lean::inc(x_64);
lean::dec(x_53);
x_67 = lean::cnstr_get(x_55, 0);
lean::inc(x_67);
lean::dec(x_55);
lean::inc(x_0);
x_71 = lean::apply_2(x_0, x_67, x_61);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_76; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_29);
lean::dec(x_64);
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
lean::dec(x_71);
x_79 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_81 = x_72;
} else {
 lean::inc(x_79);
 lean::dec(x_72);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
x_9 = x_82;
x_10 = x_76;
goto lbl_11;
}
else
{
obj* x_84; obj* x_89; obj* x_90; 
lean::dec(x_72);
x_84 = lean::cnstr_get(x_71, 1);
lean::inc(x_84);
lean::dec(x_71);
lean::inc(x_2);
lean::inc(x_0);
x_89 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_0, x_2, x_84);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
if (lean::obj_tag(x_90) == 0)
{
obj* x_94; obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_29);
lean::dec(x_64);
x_94 = lean::cnstr_get(x_89, 1);
lean::inc(x_94);
lean::dec(x_89);
x_97 = lean::cnstr_get(x_90, 0);
if (lean::is_exclusive(x_90)) {
 x_99 = x_90;
} else {
 lean::inc(x_97);
 lean::dec(x_90);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
x_9 = x_100;
x_10 = x_94;
goto lbl_11;
}
else
{
obj* x_101; 
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 x_101 = x_90;
} else {
 lean::dec(x_90);
 x_101 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_104; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_29);
lean::dec(x_64);
x_104 = lean::cnstr_get(x_89, 1);
lean::inc(x_104);
lean::dec(x_89);
lean::inc(x_4);
x_108 = l_list_reverse___rarg(x_4);
x_109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
if (lean::is_scalar(x_101)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_101;
}
lean::cnstr_set(x_110, 0, x_109);
x_9 = x_110;
x_10 = x_104;
goto lbl_11;
}
else
{
obj* x_111; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_111 = lean::cnstr_get(x_89, 1);
lean::inc(x_111);
lean::dec(x_89);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_64);
lean::cnstr_set(x_114, 1, x_29);
x_115 = l_list_reverse___rarg(x_114);
x_116 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_116, 0, x_115);
if (lean::is_scalar(x_101)) {
 x_117 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_117 = x_101;
}
lean::cnstr_set(x_117, 0, x_116);
x_9 = x_117;
x_10 = x_111;
goto lbl_11;
}
}
}
}
else
{
obj* x_118; obj* x_121; obj* x_124; obj* x_127; obj* x_129; obj* x_131; obj* x_132; obj* x_134; obj* x_135; 
x_118 = lean::cnstr_get(x_55, 0);
lean::inc(x_118);
lean::dec(x_55);
x_121 = lean::cnstr_get(x_52, 1);
lean::inc(x_121);
lean::dec(x_52);
x_124 = lean::cnstr_get(x_53, 0);
lean::inc(x_124);
lean::dec(x_53);
x_127 = lean::cnstr_get(x_118, 0);
x_129 = lean::cnstr_get(x_118, 1);
if (lean::is_exclusive(x_118)) {
 lean::cnstr_set(x_118, 0, lean::box(0));
 lean::cnstr_set(x_118, 1, lean::box(0));
 x_131 = x_118;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::dec(x_118);
 x_131 = lean::box(0);
}
x_132 = l_list_reverse___rarg(x_129);
lean::inc(x_0);
x_134 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(x_0, x_132, x_121);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_145; obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_48);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_131);
lean::dec(x_124);
lean::dec(x_127);
x_145 = lean::cnstr_get(x_134, 1);
lean::inc(x_145);
lean::dec(x_134);
x_148 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_150 = x_135;
} else {
 lean::inc(x_148);
 lean::dec(x_135);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_9 = x_151;
x_10 = x_145;
goto lbl_11;
}
else
{
obj* x_152; obj* x_153; obj* x_155; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 x_152 = x_135;
} else {
 lean::dec(x_135);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_134, 1);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_set(x_134, 1, lean::box(0));
 x_155 = x_134;
} else {
 lean::inc(x_153);
 lean::dec(x_134);
 x_155 = lean::box(0);
}
lean::inc(x_27);
lean::inc(x_124);
x_158 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_158, 0, x_124);
lean::closure_set(x_158, 1, x_27);
x_159 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2;
x_160 = l_lean_profileit__pure___rarg(x_159, x_48, x_158, x_153);
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
if (lean::obj_tag(x_161) == 0)
{
lean::dec(x_48);
lean::dec(x_152);
if (x_1 == 0)
{
obj* x_167; obj* x_169; obj* x_170; obj* x_174; obj* x_175; 
lean::dec(x_29);
lean::dec(x_124);
x_167 = lean::cnstr_get(x_160, 1);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_release(x_160, 0);
 lean::cnstr_set(x_160, 1, lean::box(0));
 x_169 = x_160;
} else {
 lean::inc(x_167);
 lean::dec(x_160);
 x_169 = lean::box(0);
}
x_170 = lean::cnstr_get(x_161, 0);
lean::inc(x_170);
lean::dec(x_161);
lean::inc(x_0);
x_174 = lean::apply_2(x_0, x_170, x_167);
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
if (lean::obj_tag(x_175) == 0)
{
obj* x_184; obj* x_187; obj* x_189; obj* x_190; 
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_27);
lean::dec(x_155);
lean::dec(x_169);
lean::dec(x_131);
lean::dec(x_127);
x_184 = lean::cnstr_get(x_174, 1);
lean::inc(x_184);
lean::dec(x_174);
x_187 = lean::cnstr_get(x_175, 0);
if (lean::is_exclusive(x_175)) {
 x_189 = x_175;
} else {
 lean::inc(x_187);
 lean::dec(x_175);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
x_9 = x_190;
x_10 = x_184;
goto lbl_11;
}
else
{
obj* x_191; obj* x_192; obj* x_194; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 x_191 = x_175;
} else {
 lean::dec(x_175);
 x_191 = lean::box(0);
}
x_192 = lean::cnstr_get(x_174, 1);
if (lean::is_exclusive(x_174)) {
 lean::cnstr_release(x_174, 0);
 x_194 = x_174;
} else {
 lean::inc(x_192);
 lean::dec(x_174);
 x_194 = lean::box(0);
}
lean::inc(x_4);
if (lean::is_scalar(x_194)) {
 x_196 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_196 = x_194;
}
lean::cnstr_set(x_196, 0, x_27);
lean::cnstr_set(x_196, 1, x_4);
if (lean::is_scalar(x_169)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_169;
}
lean::cnstr_set(x_197, 0, x_24);
lean::cnstr_set(x_197, 1, x_196);
if (lean::is_scalar(x_155)) {
 x_198 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_198 = x_155;
}
lean::cnstr_set(x_198, 0, x_21);
lean::cnstr_set(x_198, 1, x_197);
if (lean::is_scalar(x_131)) {
 x_199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_199 = x_131;
}
lean::cnstr_set(x_199, 0, x_127);
lean::cnstr_set(x_199, 1, x_198);
x_200 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_200, 0, x_199);
if (lean::is_scalar(x_191)) {
 x_201 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_201 = x_191;
}
lean::cnstr_set(x_201, 0, x_200);
x_9 = x_201;
x_10 = x_192;
goto lbl_11;
}
}
else
{
obj* x_202; obj* x_204; obj* x_205; obj* x_209; obj* x_210; 
x_202 = lean::cnstr_get(x_160, 1);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_release(x_160, 0);
 lean::cnstr_set(x_160, 1, lean::box(0));
 x_204 = x_160;
} else {
 lean::inc(x_202);
 lean::dec(x_160);
 x_204 = lean::box(0);
}
x_205 = lean::cnstr_get(x_161, 0);
lean::inc(x_205);
lean::dec(x_161);
lean::inc(x_0);
x_209 = lean::apply_2(x_0, x_205, x_202);
x_210 = lean::cnstr_get(x_209, 0);
lean::inc(x_210);
if (lean::obj_tag(x_210) == 0)
{
obj* x_221; obj* x_224; obj* x_226; obj* x_227; 
lean::dec(x_204);
lean::dec(x_21);
lean::dec(x_24);
lean::dec(x_27);
lean::dec(x_29);
lean::dec(x_155);
lean::dec(x_131);
lean::dec(x_124);
lean::dec(x_127);
x_221 = lean::cnstr_get(x_209, 1);
lean::inc(x_221);
lean::dec(x_209);
x_224 = lean::cnstr_get(x_210, 0);
if (lean::is_exclusive(x_210)) {
 x_226 = x_210;
} else {
 lean::inc(x_224);
 lean::dec(x_210);
 x_226 = lean::box(0);
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_224);
x_9 = x_227;
x_10 = x_221;
goto lbl_11;
}
else
{
obj* x_228; obj* x_229; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
if (lean::is_exclusive(x_210)) {
 lean::cnstr_release(x_210, 0);
 x_228 = x_210;
} else {
 lean::dec(x_210);
 x_228 = lean::box(0);
}
x_229 = lean::cnstr_get(x_209, 1);
if (lean::is_exclusive(x_209)) {
 lean::cnstr_release(x_209, 0);
 x_231 = x_209;
} else {
 lean::inc(x_229);
 lean::dec(x_209);
 x_231 = lean::box(0);
}
x_232 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_232, 0, x_124);
lean::cnstr_set(x_232, 1, x_29);
if (lean::is_scalar(x_231)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_231;
}
lean::cnstr_set(x_233, 0, x_27);
lean::cnstr_set(x_233, 1, x_232);
if (lean::is_scalar(x_204)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_204;
}
lean::cnstr_set(x_234, 0, x_24);
lean::cnstr_set(x_234, 1, x_233);
if (lean::is_scalar(x_155)) {
 x_235 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_235 = x_155;
}
lean::cnstr_set(x_235, 0, x_21);
lean::cnstr_set(x_235, 1, x_234);
if (lean::is_scalar(x_131)) {
 x_236 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_236 = x_131;
}
lean::cnstr_set(x_236, 0, x_127);
lean::cnstr_set(x_236, 1, x_235);
x_237 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_237, 0, x_236);
if (lean::is_scalar(x_228)) {
 x_238 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_238 = x_228;
}
lean::cnstr_set(x_238, 0, x_237);
x_9 = x_238;
x_10 = x_229;
goto lbl_11;
}
}
}
else
{
obj* x_242; obj* x_244; obj* x_245; obj* x_247; obj* x_250; obj* x_251; obj* x_252; obj* x_254; obj* x_256; obj* x_258; obj* x_259; obj* x_261; obj* x_263; obj* x_264; obj* x_266; obj* x_268; obj* x_269; obj* x_271; 
lean::dec(x_24);
lean::dec(x_27);
lean::dec(x_131);
x_242 = lean::cnstr_get(x_160, 1);
if (lean::is_exclusive(x_160)) {
 lean::cnstr_release(x_160, 0);
 lean::cnstr_set(x_160, 1, lean::box(0));
 x_244 = x_160;
} else {
 lean::inc(x_242);
 lean::dec(x_160);
 x_244 = lean::box(0);
}
x_245 = lean::cnstr_get(x_161, 0);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_set(x_161, 0, lean::box(0));
 x_247 = x_161;
} else {
 lean::inc(x_245);
 lean::dec(x_161);
 x_247 = lean::box(0);
}
lean::inc(x_245);
lean::inc(x_3);
x_250 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_250, 0, x_3);
lean::closure_set(x_250, 1, x_21);
lean::closure_set(x_250, 2, x_245);
x_251 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3;
x_252 = l_lean_profileit__pure___rarg(x_251, x_48, x_250, x_242);
lean::dec(x_48);
x_254 = lean::cnstr_get(x_252, 0);
x_256 = lean::cnstr_get(x_252, 1);
if (lean::is_exclusive(x_252)) {
 lean::cnstr_set(x_252, 0, lean::box(0));
 lean::cnstr_set(x_252, 1, lean::box(0));
 x_258 = x_252;
} else {
 lean::inc(x_254);
 lean::inc(x_256);
 lean::dec(x_252);
 x_258 = lean::box(0);
}
x_259 = lean::cnstr_get(x_254, 5);
lean::inc(x_259);
x_261 = l_list_reverse___rarg(x_259);
lean::inc(x_0);
x_263 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_0, x_261, x_256);
x_264 = lean::cnstr_get(x_263, 0);
x_266 = lean::cnstr_get(x_263, 1);
if (lean::is_exclusive(x_263)) {
 lean::cnstr_set(x_263, 0, lean::box(0));
 lean::cnstr_set(x_263, 1, lean::box(0));
 x_268 = x_263;
} else {
 lean::inc(x_264);
 lean::inc(x_266);
 lean::dec(x_263);
 x_268 = lean::box(0);
}
if (lean::obj_tag(x_264) == 0)
{
obj* x_284; obj* x_286; obj* x_287; 
lean::dec(x_258);
lean::dec(x_247);
lean::dec(x_244);
lean::dec(x_245);
lean::dec(x_268);
lean::dec(x_254);
lean::dec(x_29);
lean::dec(x_152);
lean::dec(x_155);
lean::dec(x_124);
lean::dec(x_127);
x_284 = lean::cnstr_get(x_264, 0);
if (lean::is_exclusive(x_264)) {
 x_286 = x_264;
} else {
 lean::inc(x_284);
 lean::dec(x_264);
 x_286 = lean::box(0);
}
if (lean::is_scalar(x_286)) {
 x_287 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_287 = x_286;
}
lean::cnstr_set(x_287, 0, x_284);
x_9 = x_287;
x_10 = x_266;
goto lbl_11;
}
else
{
obj* x_289; uint8 x_290; 
lean::dec(x_264);
x_289 = l_lean_parser_module_eoi;
x_290 = l_lean_parser_syntax_is__of__kind___main(x_289, x_245);
lean::dec(x_245);
if (x_290 == 0)
{
obj* x_293; 
lean::dec(x_152);
x_293 = lean::box(0);
x_269 = x_293;
goto lbl_270;
}
else
{
obj* x_301; 
lean::dec(x_258);
lean::dec(x_247);
lean::dec(x_244);
lean::dec(x_268);
lean::dec(x_254);
lean::dec(x_155);
lean::dec(x_127);
x_301 = lean::box(0);
x_271 = x_301;
goto lbl_272;
}
}
lbl_270:
{
lean::dec(x_269);
if (x_1 == 0)
{
obj* x_305; obj* x_307; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; 
lean::dec(x_29);
lean::dec(x_124);
x_305 = lean::cnstr_get(x_254, 6);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_254, 7);
lean::inc(x_307);
lean::inc(x_4);
if (lean::is_scalar(x_268)) {
 x_310 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_310 = x_268;
}
lean::cnstr_set(x_310, 0, x_307);
lean::cnstr_set(x_310, 1, x_4);
if (lean::is_scalar(x_258)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_258;
}
lean::cnstr_set(x_311, 0, x_305);
lean::cnstr_set(x_311, 1, x_310);
if (lean::is_scalar(x_244)) {
 x_312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_312 = x_244;
}
lean::cnstr_set(x_312, 0, x_254);
lean::cnstr_set(x_312, 1, x_311);
if (lean::is_scalar(x_155)) {
 x_313 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_313 = x_155;
}
lean::cnstr_set(x_313, 0, x_127);
lean::cnstr_set(x_313, 1, x_312);
x_314 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_314, 0, x_313);
if (lean::is_scalar(x_247)) {
 x_315 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_315 = x_247;
}
lean::cnstr_set(x_315, 0, x_314);
x_9 = x_315;
x_10 = x_266;
goto lbl_11;
}
else
{
obj* x_316; obj* x_318; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; 
x_316 = lean::cnstr_get(x_254, 6);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_254, 7);
lean::inc(x_318);
x_320 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_320, 0, x_124);
lean::cnstr_set(x_320, 1, x_29);
if (lean::is_scalar(x_268)) {
 x_321 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_321 = x_268;
}
lean::cnstr_set(x_321, 0, x_318);
lean::cnstr_set(x_321, 1, x_320);
if (lean::is_scalar(x_258)) {
 x_322 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_322 = x_258;
}
lean::cnstr_set(x_322, 0, x_316);
lean::cnstr_set(x_322, 1, x_321);
if (lean::is_scalar(x_244)) {
 x_323 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_323 = x_244;
}
lean::cnstr_set(x_323, 0, x_254);
lean::cnstr_set(x_323, 1, x_322);
if (lean::is_scalar(x_155)) {
 x_324 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_324 = x_155;
}
lean::cnstr_set(x_324, 0, x_127);
lean::cnstr_set(x_324, 1, x_323);
x_325 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_325, 0, x_324);
if (lean::is_scalar(x_247)) {
 x_326 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_326 = x_247;
}
lean::cnstr_set(x_326, 0, x_325);
x_9 = x_326;
x_10 = x_266;
goto lbl_11;
}
}
lbl_272:
{
lean::dec(x_271);
if (x_1 == 0)
{
obj* x_331; obj* x_332; obj* x_333; 
lean::dec(x_29);
lean::dec(x_124);
lean::inc(x_4);
x_331 = l_list_reverse___rarg(x_4);
x_332 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_332, 0, x_331);
if (lean::is_scalar(x_152)) {
 x_333 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_333 = x_152;
}
lean::cnstr_set(x_333, 0, x_332);
x_9 = x_333;
x_10 = x_266;
goto lbl_11;
}
else
{
obj* x_334; obj* x_335; obj* x_336; obj* x_337; 
x_334 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_334, 0, x_124);
lean::cnstr_set(x_334, 1, x_29);
x_335 = l_list_reverse___rarg(x_334);
x_336 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_336, 0, x_335);
if (lean::is_scalar(x_152)) {
 x_337 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_337 = x_152;
}
lean::cnstr_set(x_337, 0, x_336);
x_9 = x_337;
x_10 = x_266;
goto lbl_11;
}
}
}
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_342; obj* x_344; obj* x_345; obj* x_346; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_342 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_344 = x_9;
} else {
 lean::inc(x_342);
 lean::dec(x_9);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_342);
x_346 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_346, 0, x_345);
lean::cnstr_set(x_346, 1, x_10);
return x_346;
}
else
{
obj* x_347; obj* x_349; 
x_347 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 x_349 = x_9;
} else {
 lean::inc(x_347);
 lean::dec(x_9);
 x_349 = lean::box(0);
}
if (lean::obj_tag(x_347) == 0)
{
obj* x_351; 
lean::dec(x_349);
x_351 = lean::cnstr_get(x_347, 0);
lean::inc(x_351);
lean::dec(x_347);
x_5 = x_0;
x_6 = x_0;
x_7 = x_351;
x_8 = x_10;
goto _start;
}
else
{
obj* x_359; obj* x_362; obj* x_363; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_359 = lean::cnstr_get(x_347, 0);
lean::inc(x_359);
lean::dec(x_347);
if (lean::is_scalar(x_349)) {
 x_362 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_362 = x_349;
}
lean::cnstr_set(x_362, 0, x_359);
x_363 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_10);
return x_363;
}
}
}
}
}
obj* _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("as_messages");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_lean_options_mk;
x_6 = 1;
x_7 = l_lean_kvmap_set__bool(x_5, x_4, x_6);
return x_7;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_14 = l_lean_expander_builtin__transformers;
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_9);
lean::cnstr_set(x_15, 1, x_14);
x_16 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___closed__1;
lean::inc(x_12);
x_18 = l_lean_elaborator_mk__state(x_12, x_16);
lean::inc(x_13);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_13);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_3);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6(x_0, x_1, x_5, x_12, x_13, lean::box(0), lean::box(0), x_23, x_6);
return x_24;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___boxed), 14, 0);
return x_2;
}
}
obj* l_lean_run__frontend(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_10; 
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_lean_mk__config(x_0, x_1);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_13 = x_10;
} else {
 lean::inc(x_11);
 lean::dec(x_10);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
lean::inc(x_4);
x_5 = x_14;
x_6 = x_4;
goto lbl_7;
}
else
{
obj* x_16; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
lean::inc(x_4);
x_5 = x_19;
x_6 = x_4;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_6);
return x_28;
}
else
{
obj* x_29; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_5, 0);
lean::inc(x_29);
lean::dec(x_5);
lean::inc(x_29);
x_33 = l_lean_parser_parse__header(x_29);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_34, 0);
lean::inc(x_40);
lean::dec(x_34);
x_43 = lean::apply_2(x_2, x_40, x_6);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_46 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_51 = x_44;
} else {
 lean::inc(x_49);
 lean::dec(x_44);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_48)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_48;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_44);
x_55 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_57 = x_43;
} else {
 lean::inc(x_55);
 lean::dec(x_43);
 x_57 = lean::box(0);
}
x_58 = l_lean_expander_expand__bracketed__binder___main___closed__8;
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
}
else
{
obj* x_60; obj* x_63; obj* x_65; obj* x_69; obj* x_72; obj* x_73; 
x_60 = lean::cnstr_get(x_34, 0);
lean::inc(x_60);
lean::dec(x_34);
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 1);
lean::inc(x_65);
lean::dec(x_60);
lean::inc(x_65);
x_69 = l_list_reverse___rarg(x_65);
lean::inc(x_69);
lean::inc(x_2);
x_72 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_69, x_6);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
if (lean::obj_tag(x_73) == 0)
{
obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_65);
lean::dec(x_63);
lean::dec(x_69);
lean::dec(x_29);
x_82 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 x_84 = x_72;
} else {
 lean::inc(x_82);
 lean::dec(x_72);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_87 = x_73;
} else {
 lean::inc(x_85);
 lean::dec(x_73);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
if (lean::is_scalar(x_84)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_84;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_82);
return x_89;
}
else
{
obj* x_91; obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_73);
x_91 = lean::cnstr_get(x_72, 1);
lean::inc(x_91);
lean::dec(x_72);
x_94 = lean::cnstr_get(x_29, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_94, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_96, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_98, 2);
lean::inc(x_100);
lean::inc(x_100);
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_0);
lean::cnstr_set(x_103, 1, x_1);
lean::cnstr_set(x_103, 2, x_100);
lean::inc(x_29);
lean::inc(x_103);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_29);
x_107 = lean::box(0);
x_108 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(x_2, x_3, x_29, x_63, x_65, x_69, x_91, x_94, x_96, x_98, x_100, x_103, x_106, x_107);
lean::dec(x_103);
lean::dec(x_100);
lean::dec(x_96);
lean::dec(x_94);
lean::dec(x_65);
return x_108;
}
}
}
}
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_1);
x_10 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6(x_0, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_6);
return x_10;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10, obj* x_11, obj* x_12, obj* x_13) {
_start:
{
uint8 x_14; obj* x_15; 
x_14 = lean::unbox(x_1);
x_15 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(x_0, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean::dec(x_4);
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_11);
return x_15;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_run__frontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
x_6 = l_lean_run__frontend(x_0, x_1, x_2, x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_io_prim_put_str(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_18 = x_3;
} else {
 lean::inc(x_16);
 lean::dec(x_3);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
}
obj* l_io_print___at_lean_process__file___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_lean_process__file___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
x_17 = l_lean_format_be___main___closed__1;
x_18 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_17, x_14);
return x_18;
}
}
}
obj* _init_l_lean_process__file___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
return x_0;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"pos_col\": ");
return x_0;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"severity\": ");
return x_0;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("information");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"caption\": ");
return x_0;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"text\": ");
return x_0;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("warning");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("error");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* l_lean_process__file___lambda__1(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (x_0 == 0)
{
obj* x_5; obj* x_6; 
x_5 = l_lean_message_to__string(x_1);
x_6 = l_io_println___at_lean_process__file___spec__1(x_5, x_2);
lean::dec(x_5);
return x_6;
}
else
{
obj* x_8; 
x_8 = lean::box(0);
x_3 = x_8;
goto lbl_4;
}
lbl_4:
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_35; 
lean::dec(x_3);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_14 = l_nat_repr(x_12);
x_15 = l_lean_process__file___lambda__1___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = l_lean_process__file___lambda__1___closed__2;
x_19 = lean::string_append(x_16, x_18);
x_20 = lean::cnstr_get(x_10, 1);
lean::inc(x_20);
lean::dec(x_10);
x_23 = l_nat_repr(x_20);
x_24 = lean::string_append(x_19, x_23);
lean::dec(x_23);
x_26 = l_lean_process__file___lambda__1___closed__3;
x_27 = lean::string_append(x_24, x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_29 = lean::cnstr_get(x_1, 3);
lean::inc(x_29);
x_31 = l_string_quote(x_29);
x_32 = lean::cnstr_get(x_1, 4);
lean::inc(x_32);
lean::dec(x_1);
x_35 = l_string_quote(x_32);
switch (x_28) {
case 0:
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
x_36 = l_lean_process__file___lambda__1___closed__4;
x_37 = lean::string_append(x_27, x_36);
x_38 = l_lean_process__file___lambda__1___closed__5;
x_39 = lean::string_append(x_37, x_38);
x_40 = lean::string_append(x_39, x_31);
lean::dec(x_31);
x_42 = l_lean_process__file___lambda__1___closed__6;
x_43 = lean::string_append(x_40, x_42);
x_44 = lean::string_append(x_43, x_35);
lean::dec(x_35);
x_46 = l_lean_process__file___lambda__1___closed__7;
x_47 = lean::string_append(x_44, x_46);
x_48 = l_io_println___at_lean_process__file___spec__1(x_47, x_2);
lean::dec(x_47);
return x_48;
}
case 1:
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_50 = l_lean_process__file___lambda__1___closed__8;
x_51 = lean::string_append(x_27, x_50);
x_52 = l_lean_process__file___lambda__1___closed__5;
x_53 = lean::string_append(x_51, x_52);
x_54 = lean::string_append(x_53, x_31);
lean::dec(x_31);
x_56 = l_lean_process__file___lambda__1___closed__6;
x_57 = lean::string_append(x_54, x_56);
x_58 = lean::string_append(x_57, x_35);
lean::dec(x_35);
x_60 = l_lean_process__file___lambda__1___closed__7;
x_61 = lean::string_append(x_58, x_60);
x_62 = l_io_println___at_lean_process__file___spec__1(x_61, x_2);
lean::dec(x_61);
return x_62;
}
default:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
x_64 = l_lean_process__file___lambda__1___closed__9;
x_65 = lean::string_append(x_27, x_64);
x_66 = l_lean_process__file___lambda__1___closed__5;
x_67 = lean::string_append(x_65, x_66);
x_68 = lean::string_append(x_67, x_31);
lean::dec(x_31);
x_70 = l_lean_process__file___lambda__1___closed__6;
x_71 = lean::string_append(x_68, x_70);
x_72 = lean::string_append(x_71, x_35);
lean::dec(x_35);
x_74 = l_lean_process__file___lambda__1___closed__7;
x_75 = lean::string_append(x_72, x_74);
x_76 = l_io_println___at_lean_process__file___spec__1(x_75, x_2);
lean::dec(x_75);
return x_76;
}
}
}
}
}
obj* _init_l_lean_process__file___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; 
x_0 = lean::mk_nat_obj(1u);
x_1 = l_nat_repr(x_0);
x_2 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::mk_string(", \"pos_col\": ");
x_6 = lean::string_append(x_3, x_5);
lean::dec(x_5);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_nat_repr(x_8);
x_10 = lean::string_append(x_6, x_9);
lean::dec(x_9);
x_12 = lean::mk_string(", \"severity\": ");
x_13 = lean::string_append(x_10, x_12);
lean::dec(x_12);
x_15 = lean::mk_string("error");
x_16 = l_string_quote(x_15);
x_17 = lean::string_append(x_13, x_16);
lean::dec(x_16);
x_19 = lean::mk_string(", \"caption\": ");
x_20 = lean::string_append(x_17, x_19);
lean::dec(x_19);
x_22 = lean::mk_string("");
x_23 = l_string_quote(x_22);
x_24 = lean::string_append(x_20, x_23);
lean::dec(x_23);
x_26 = lean::mk_string(", \"text\": ");
x_27 = lean::string_append(x_24, x_26);
lean::dec(x_26);
return x_27;
}
}
obj* lean_process_file(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_8; obj* x_10; 
x_4 = lean::box(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = 0;
lean::inc(x_0);
x_8 = l_lean_run__frontend(x_0, x_1, x_5, x_6, x_3);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_18; 
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
if (x_2 == 0)
{
obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_20 = lean::box(0);
x_21 = l_lean_elaborator_notation_elaborate___closed__1;
x_22 = 2;
x_23 = l_string_iterator_extract___main___closed__1;
x_24 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_21);
lean::cnstr_set(x_24, 2, x_20);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set(x_24, 4, x_15);
lean::cnstr_set_scalar(x_24, sizeof(void*)*5, x_22);
x_25 = x_24;
x_26 = l_lean_message_to__string(x_25);
x_27 = l_io_println___at_lean_process__file___spec__1(x_26, x_12);
lean::dec(x_26);
x_29 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_release(x_27, 0);
 x_31 = x_27;
} else {
 lean::inc(x_29);
 lean::dec(x_27);
 x_31 = lean::box(0);
}
x_32 = lean::box(x_6);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_0);
x_35 = lean::box(0);
x_18 = x_35;
goto lbl_19;
}
lbl_19:
{
obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_18);
x_37 = l_string_quote(x_15);
x_38 = l_lean_process__file___closed__1;
x_39 = lean::string_append(x_38, x_37);
lean::dec(x_37);
x_41 = l_lean_process__file___lambda__1___closed__7;
x_42 = lean::string_append(x_39, x_41);
x_43 = l_io_println___at_lean_process__file___spec__1(x_42, x_12);
lean::dec(x_42);
x_45 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_47 = x_43;
} else {
 lean::inc(x_45);
 lean::dec(x_43);
 x_47 = lean::box(0);
}
x_48 = lean::box(x_6);
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
else
{
obj* x_52; obj* x_54; uint8 x_55; obj* x_56; obj* x_57; 
lean::dec(x_10);
lean::dec(x_0);
x_52 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_54 = x_8;
} else {
 lean::inc(x_52);
 lean::dec(x_8);
 x_54 = lean::box(0);
}
x_55 = 1;
x_56 = lean::box(x_55);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
}
}
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_print___at_lean_process__file___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_print___at_lean_process__file___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_println___at_lean_process__file___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_println___at_lean_process__file___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_process__file___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_process__file___lambda__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_process__file___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = lean_process_file(x_0, x_1, x_4, x_3);
return x_5;
}
}
void initialize_init_default();
void initialize_init_lean_parser_module();
void initialize_init_lean_expander();
void initialize_init_lean_elaborator();
void initialize_init_lean_util();
void initialize_init_io();
static bool _G_initialized = false;
void initialize_init_lean_frontend() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_default();
 initialize_init_lean_parser_module();
 initialize_init_lean_expander();
 initialize_init_lean_elaborator();
 initialize_init_lean_util();
 initialize_init_io();
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3);
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___closed__1();
lean::mark_persistent(l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___closed__1);
 l_lean_process__file___lambda__1___closed__1 = _init_l_lean_process__file___lambda__1___closed__1();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__1);
 l_lean_process__file___lambda__1___closed__2 = _init_l_lean_process__file___lambda__1___closed__2();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__2);
 l_lean_process__file___lambda__1___closed__3 = _init_l_lean_process__file___lambda__1___closed__3();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__3);
 l_lean_process__file___lambda__1___closed__4 = _init_l_lean_process__file___lambda__1___closed__4();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__4);
 l_lean_process__file___lambda__1___closed__5 = _init_l_lean_process__file___lambda__1___closed__5();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__5);
 l_lean_process__file___lambda__1___closed__6 = _init_l_lean_process__file___lambda__1___closed__6();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__6);
 l_lean_process__file___lambda__1___closed__7 = _init_l_lean_process__file___lambda__1___closed__7();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__7);
 l_lean_process__file___lambda__1___closed__8 = _init_l_lean_process__file___lambda__1___closed__8();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__8);
 l_lean_process__file___lambda__1___closed__9 = _init_l_lean_process__file___lambda__1___closed__9();
lean::mark_persistent(l_lean_process__file___lambda__1___closed__9);
 l_lean_process__file___closed__1 = _init_l_lean_process__file___closed__1();
lean::mark_persistent(l_lean_process__file___closed__1);
}

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
obj* l___private_init_io_1__put__str___at_lean_process__file___spec__3(obj*, obj*);
obj* l_io_prim_iterate__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__6;
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_parser_parse__command(obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_lean_process__file___closed__1;
obj* l_lean_run__frontend___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_lean_process__file___closed__2;
extern obj* l_lean_parser_module_eoi;
obj* l_io_println___at_lean_process__file___spec__1___boxed(obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2;
obj* l_io_print___at_lean_process__file___spec__2___boxed(obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1(obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3(obj*, obj*, obj*, obj*);
obj* l_io_println___at_lean_process__file___spec__1(obj*, obj*);
extern obj* l_lean_options_mk;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3;
obj* l___private_init_io_1__put__str___at_lean_process__file___spec__3___boxed(obj*, obj*);
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__header(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj*, uint8, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_lean_elaborator_mk__state(obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_io_print___at_lean_process__file___spec__2(obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6(obj*, uint8, obj*, obj*, obj*, obj*, obj*);
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
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__command(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_expand(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_process__command(x_0, x_1, x_2);
return x_4;
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_25; obj* x_27; obj* x_30; obj* x_32; obj* x_35; obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_53; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_10, 0);
lean::inc(x_19);
lean::dec(x_10);
x_22 = lean::cnstr_get(x_12, 0);
lean::inc(x_22);
lean::dec(x_12);
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_14, 1);
lean::inc(x_27);
lean::dec(x_14);
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_30, 0);
lean::inc(x_32);
lean::dec(x_30);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
lean::dec(x_35);
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
lean::dec(x_41);
x_46 = l_lean_file__map_to__position(x_38, x_43);
lean::inc(x_22);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_48, 0, x_22);
lean::closure_set(x_48, 1, x_16);
x_49 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1;
x_50 = l_lean_profileit__pure___rarg(x_49, x_46, x_48, x_6);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_59; obj* x_62; obj* x_65; obj* x_69; obj* x_70; 
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_22);
lean::dec(x_46);
x_59 = lean::cnstr_get(x_50, 1);
lean::inc(x_59);
lean::dec(x_50);
x_62 = lean::cnstr_get(x_51, 0);
lean::inc(x_62);
lean::dec(x_51);
x_65 = lean::cnstr_get(x_53, 0);
lean::inc(x_65);
lean::dec(x_53);
lean::inc(x_0);
x_69 = lean::apply_2(x_0, x_65, x_59);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_78; obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_27);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_62);
x_78 = lean::cnstr_get(x_69, 1);
lean::inc(x_78);
lean::dec(x_69);
x_81 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_83 = x_70;
} else {
 lean::inc(x_81);
 lean::dec(x_70);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
x_7 = x_84;
x_8 = x_78;
goto lbl_9;
}
else
{
obj* x_86; obj* x_89; obj* x_90; 
lean::dec(x_70);
x_86 = lean::cnstr_get(x_69, 1);
lean::inc(x_86);
lean::dec(x_69);
x_89 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_0, x_1, x_86);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
if (lean::obj_tag(x_90) == 0)
{
obj* x_96; obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_62);
x_96 = lean::cnstr_get(x_89, 1);
lean::inc(x_96);
lean::dec(x_89);
x_99 = lean::cnstr_get(x_90, 0);
if (lean::is_exclusive(x_90)) {
 x_101 = x_90;
} else {
 lean::inc(x_99);
 lean::dec(x_90);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
x_7 = x_102;
x_8 = x_96;
goto lbl_9;
}
else
{
obj* x_103; 
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 x_103 = x_90;
} else {
 lean::dec(x_90);
 x_103 = lean::box(0);
}
if (x_2 == 0)
{
obj* x_106; obj* x_108; obj* x_109; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_27);
lean::dec(x_62);
x_106 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 x_108 = x_89;
} else {
 lean::inc(x_106);
 lean::dec(x_89);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_19, 8);
lean::inc(x_109);
lean::dec(x_19);
x_112 = l_list_reverse___rarg(x_3);
if (lean::is_scalar(x_108)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_108;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_109);
x_114 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_114, 0, x_113);
if (lean::is_scalar(x_103)) {
 x_115 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_115 = x_103;
}
lean::cnstr_set(x_115, 0, x_114);
x_7 = x_115;
x_8 = x_106;
goto lbl_9;
}
else
{
obj* x_117; obj* x_119; obj* x_120; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_3);
x_117 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 x_119 = x_89;
} else {
 lean::inc(x_117);
 lean::dec(x_89);
 x_119 = lean::box(0);
}
x_120 = lean::cnstr_get(x_19, 8);
lean::inc(x_120);
lean::dec(x_19);
x_123 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_123, 0, x_62);
lean::cnstr_set(x_123, 1, x_27);
x_124 = l_list_reverse___rarg(x_123);
if (lean::is_scalar(x_119)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_119;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_120);
x_126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_126, 0, x_125);
if (lean::is_scalar(x_103)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_103;
}
lean::cnstr_set(x_127, 0, x_126);
x_7 = x_127;
x_8 = x_117;
goto lbl_9;
}
}
}
}
else
{
obj* x_129; obj* x_132; obj* x_135; obj* x_138; obj* x_140; obj* x_142; obj* x_143; obj* x_145; obj* x_146; 
lean::dec(x_1);
x_129 = lean::cnstr_get(x_53, 0);
lean::inc(x_129);
lean::dec(x_53);
x_132 = lean::cnstr_get(x_50, 1);
lean::inc(x_132);
lean::dec(x_50);
x_135 = lean::cnstr_get(x_51, 0);
lean::inc(x_135);
lean::dec(x_51);
x_138 = lean::cnstr_get(x_129, 0);
x_140 = lean::cnstr_get(x_129, 1);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_set(x_129, 0, lean::box(0));
 lean::cnstr_set(x_129, 1, lean::box(0));
 x_142 = x_129;
} else {
 lean::inc(x_138);
 lean::inc(x_140);
 lean::dec(x_129);
 x_142 = lean::box(0);
}
x_143 = l_list_reverse___rarg(x_140);
lean::inc(x_0);
x_145 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(x_0, x_143, x_132);
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
if (lean::obj_tag(x_146) == 0)
{
obj* x_159; obj* x_162; obj* x_164; obj* x_165; 
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_46);
lean::dec(x_138);
lean::dec(x_135);
lean::dec(x_142);
x_159 = lean::cnstr_get(x_145, 1);
lean::inc(x_159);
lean::dec(x_145);
x_162 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_164 = x_146;
} else {
 lean::inc(x_162);
 lean::dec(x_146);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
x_7 = x_165;
x_8 = x_159;
goto lbl_9;
}
else
{
obj* x_167; obj* x_169; obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
lean::dec(x_146);
x_167 = lean::cnstr_get(x_145, 1);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_set(x_145, 1, lean::box(0));
 x_169 = x_145;
} else {
 lean::inc(x_167);
 lean::dec(x_145);
 x_169 = lean::box(0);
}
lean::inc(x_25);
lean::inc(x_135);
x_172 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_172, 0, x_135);
lean::closure_set(x_172, 1, x_25);
x_173 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2;
x_174 = l_lean_profileit__pure___rarg(x_173, x_46, x_172, x_167);
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
if (lean::obj_tag(x_175) == 0)
{
lean::dec(x_4);
lean::dec(x_46);
if (x_2 == 0)
{
obj* x_181; obj* x_183; obj* x_184; obj* x_187; obj* x_188; 
lean::dec(x_27);
lean::dec(x_135);
x_181 = lean::cnstr_get(x_174, 1);
if (lean::is_exclusive(x_174)) {
 lean::cnstr_release(x_174, 0);
 lean::cnstr_set(x_174, 1, lean::box(0));
 x_183 = x_174;
} else {
 lean::inc(x_181);
 lean::dec(x_174);
 x_183 = lean::box(0);
}
x_184 = lean::cnstr_get(x_175, 0);
lean::inc(x_184);
lean::dec(x_175);
x_187 = lean::apply_2(x_0, x_184, x_181);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
obj* x_198; obj* x_201; obj* x_203; obj* x_204; 
lean::dec(x_25);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_169);
lean::dec(x_183);
lean::dec(x_138);
lean::dec(x_142);
x_198 = lean::cnstr_get(x_187, 1);
lean::inc(x_198);
lean::dec(x_187);
x_201 = lean::cnstr_get(x_188, 0);
if (lean::is_exclusive(x_188)) {
 x_203 = x_188;
} else {
 lean::inc(x_201);
 lean::dec(x_188);
 x_203 = lean::box(0);
}
if (lean::is_scalar(x_203)) {
 x_204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_204 = x_203;
}
lean::cnstr_set(x_204, 0, x_201);
x_7 = x_204;
x_8 = x_198;
goto lbl_9;
}
else
{
obj* x_205; obj* x_206; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 x_205 = x_188;
} else {
 lean::dec(x_188);
 x_205 = lean::box(0);
}
x_206 = lean::cnstr_get(x_187, 1);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 x_208 = x_187;
} else {
 lean::inc(x_206);
 lean::dec(x_187);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_25);
lean::cnstr_set(x_209, 1, x_3);
if (lean::is_scalar(x_183)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_183;
}
lean::cnstr_set(x_210, 0, x_22);
lean::cnstr_set(x_210, 1, x_209);
if (lean::is_scalar(x_169)) {
 x_211 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_211 = x_169;
}
lean::cnstr_set(x_211, 0, x_19);
lean::cnstr_set(x_211, 1, x_210);
if (lean::is_scalar(x_142)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_142;
}
lean::cnstr_set(x_212, 0, x_138);
lean::cnstr_set(x_212, 1, x_211);
x_213 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_213, 0, x_212);
if (lean::is_scalar(x_205)) {
 x_214 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_214 = x_205;
}
lean::cnstr_set(x_214, 0, x_213);
x_7 = x_214;
x_8 = x_206;
goto lbl_9;
}
}
else
{
obj* x_216; obj* x_218; obj* x_219; obj* x_222; obj* x_223; 
lean::dec(x_3);
x_216 = lean::cnstr_get(x_174, 1);
if (lean::is_exclusive(x_174)) {
 lean::cnstr_release(x_174, 0);
 lean::cnstr_set(x_174, 1, lean::box(0));
 x_218 = x_174;
} else {
 lean::inc(x_216);
 lean::dec(x_174);
 x_218 = lean::box(0);
}
x_219 = lean::cnstr_get(x_175, 0);
lean::inc(x_219);
lean::dec(x_175);
x_222 = lean::apply_2(x_0, x_219, x_216);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
if (lean::obj_tag(x_223) == 0)
{
obj* x_234; obj* x_237; obj* x_239; obj* x_240; 
lean::dec(x_218);
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_169);
lean::dec(x_138);
lean::dec(x_135);
lean::dec(x_142);
x_234 = lean::cnstr_get(x_222, 1);
lean::inc(x_234);
lean::dec(x_222);
x_237 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_239 = x_223;
} else {
 lean::inc(x_237);
 lean::dec(x_223);
 x_239 = lean::box(0);
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_237);
x_7 = x_240;
x_8 = x_234;
goto lbl_9;
}
else
{
obj* x_241; obj* x_242; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 x_241 = x_223;
} else {
 lean::dec(x_223);
 x_241 = lean::box(0);
}
x_242 = lean::cnstr_get(x_222, 1);
if (lean::is_exclusive(x_222)) {
 lean::cnstr_release(x_222, 0);
 x_244 = x_222;
} else {
 lean::inc(x_242);
 lean::dec(x_222);
 x_244 = lean::box(0);
}
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_135);
lean::cnstr_set(x_245, 1, x_27);
if (lean::is_scalar(x_244)) {
 x_246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_246 = x_244;
}
lean::cnstr_set(x_246, 0, x_25);
lean::cnstr_set(x_246, 1, x_245);
if (lean::is_scalar(x_218)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_218;
}
lean::cnstr_set(x_247, 0, x_22);
lean::cnstr_set(x_247, 1, x_246);
if (lean::is_scalar(x_169)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_169;
}
lean::cnstr_set(x_248, 0, x_19);
lean::cnstr_set(x_248, 1, x_247);
if (lean::is_scalar(x_142)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_142;
}
lean::cnstr_set(x_249, 0, x_138);
lean::cnstr_set(x_249, 1, x_248);
x_250 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_250, 0, x_249);
if (lean::is_scalar(x_241)) {
 x_251 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_251 = x_241;
}
lean::cnstr_set(x_251, 0, x_250);
x_7 = x_251;
x_8 = x_242;
goto lbl_9;
}
}
}
else
{
obj* x_255; obj* x_257; obj* x_258; obj* x_262; obj* x_263; obj* x_264; obj* x_266; obj* x_268; obj* x_270; obj* x_271; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_25);
lean::dec(x_22);
lean::dec(x_142);
x_255 = lean::cnstr_get(x_174, 1);
if (lean::is_exclusive(x_174)) {
 lean::cnstr_release(x_174, 0);
 lean::cnstr_set(x_174, 1, lean::box(0));
 x_257 = x_174;
} else {
 lean::inc(x_255);
 lean::dec(x_174);
 x_257 = lean::box(0);
}
x_258 = lean::cnstr_get(x_175, 0);
lean::inc(x_258);
lean::dec(x_175);
lean::inc(x_258);
x_262 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_262, 0, x_4);
lean::closure_set(x_262, 1, x_19);
lean::closure_set(x_262, 2, x_258);
x_263 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3;
x_264 = l_lean_profileit__pure___rarg(x_263, x_46, x_262, x_255);
lean::dec(x_46);
x_266 = lean::cnstr_get(x_264, 0);
x_268 = lean::cnstr_get(x_264, 1);
if (lean::is_exclusive(x_264)) {
 lean::cnstr_set(x_264, 0, lean::box(0));
 lean::cnstr_set(x_264, 1, lean::box(0));
 x_270 = x_264;
} else {
 lean::inc(x_266);
 lean::inc(x_268);
 lean::dec(x_264);
 x_270 = lean::box(0);
}
x_271 = lean::cnstr_get(x_266, 5);
lean::inc(x_271);
x_273 = l_list_reverse___rarg(x_271);
x_274 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_0, x_273, x_268);
x_275 = lean::cnstr_get(x_274, 0);
lean::inc(x_275);
if (lean::obj_tag(x_275) == 0)
{
obj* x_286; obj* x_289; obj* x_291; obj* x_292; 
lean::dec(x_266);
lean::dec(x_257);
lean::dec(x_258);
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_270);
lean::dec(x_169);
lean::dec(x_138);
lean::dec(x_135);
x_286 = lean::cnstr_get(x_274, 1);
lean::inc(x_286);
lean::dec(x_274);
x_289 = lean::cnstr_get(x_275, 0);
if (lean::is_exclusive(x_275)) {
 x_291 = x_275;
} else {
 lean::inc(x_289);
 lean::dec(x_275);
 x_291 = lean::box(0);
}
if (lean::is_scalar(x_291)) {
 x_292 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_292 = x_291;
}
lean::cnstr_set(x_292, 0, x_289);
x_7 = x_292;
x_8 = x_286;
goto lbl_9;
}
else
{
obj* x_293; obj* x_294; obj* x_296; obj* x_297; uint8 x_298; 
if (lean::is_exclusive(x_275)) {
 lean::cnstr_release(x_275, 0);
 x_293 = x_275;
} else {
 lean::dec(x_275);
 x_293 = lean::box(0);
}
x_294 = lean::cnstr_get(x_274, 1);
if (lean::is_exclusive(x_274)) {
 lean::cnstr_release(x_274, 0);
 lean::cnstr_set(x_274, 1, lean::box(0));
 x_296 = x_274;
} else {
 lean::inc(x_294);
 lean::dec(x_274);
 x_296 = lean::box(0);
}
x_297 = l_lean_parser_module_eoi;
x_298 = l_lean_parser_syntax_is__of__kind___main(x_297, x_258);
lean::dec(x_258);
if (x_298 == 0)
{
if (x_2 == 0)
{
obj* x_302; obj* x_304; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; 
lean::dec(x_27);
lean::dec(x_135);
x_302 = lean::cnstr_get(x_266, 6);
lean::inc(x_302);
x_304 = lean::cnstr_get(x_266, 7);
lean::inc(x_304);
if (lean::is_scalar(x_296)) {
 x_306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_306 = x_296;
}
lean::cnstr_set(x_306, 0, x_304);
lean::cnstr_set(x_306, 1, x_3);
if (lean::is_scalar(x_270)) {
 x_307 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_307 = x_270;
}
lean::cnstr_set(x_307, 0, x_302);
lean::cnstr_set(x_307, 1, x_306);
if (lean::is_scalar(x_257)) {
 x_308 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_308 = x_257;
}
lean::cnstr_set(x_308, 0, x_266);
lean::cnstr_set(x_308, 1, x_307);
if (lean::is_scalar(x_169)) {
 x_309 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_309 = x_169;
}
lean::cnstr_set(x_309, 0, x_138);
lean::cnstr_set(x_309, 1, x_308);
x_310 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_310, 0, x_309);
if (lean::is_scalar(x_293)) {
 x_311 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_311 = x_293;
}
lean::cnstr_set(x_311, 0, x_310);
x_7 = x_311;
x_8 = x_294;
goto lbl_9;
}
else
{
obj* x_313; obj* x_315; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; 
lean::dec(x_3);
x_313 = lean::cnstr_get(x_266, 6);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_266, 7);
lean::inc(x_315);
x_317 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_317, 0, x_135);
lean::cnstr_set(x_317, 1, x_27);
if (lean::is_scalar(x_296)) {
 x_318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_318 = x_296;
}
lean::cnstr_set(x_318, 0, x_315);
lean::cnstr_set(x_318, 1, x_317);
if (lean::is_scalar(x_270)) {
 x_319 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_319 = x_270;
}
lean::cnstr_set(x_319, 0, x_313);
lean::cnstr_set(x_319, 1, x_318);
if (lean::is_scalar(x_257)) {
 x_320 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_320 = x_257;
}
lean::cnstr_set(x_320, 0, x_266);
lean::cnstr_set(x_320, 1, x_319);
if (lean::is_scalar(x_169)) {
 x_321 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_321 = x_169;
}
lean::cnstr_set(x_321, 0, x_138);
lean::cnstr_set(x_321, 1, x_320);
x_322 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_322, 0, x_321);
if (lean::is_scalar(x_293)) {
 x_323 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_323 = x_293;
}
lean::cnstr_set(x_323, 0, x_322);
x_7 = x_323;
x_8 = x_294;
goto lbl_9;
}
}
else
{
lean::dec(x_257);
lean::dec(x_270);
lean::dec(x_169);
lean::dec(x_138);
if (x_2 == 0)
{
obj* x_330; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_27);
lean::dec(x_135);
x_330 = lean::cnstr_get(x_266, 8);
lean::inc(x_330);
lean::dec(x_266);
x_333 = l_list_reverse___rarg(x_3);
if (lean::is_scalar(x_296)) {
 x_334 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_334 = x_296;
}
lean::cnstr_set(x_334, 0, x_333);
lean::cnstr_set(x_334, 1, x_330);
x_335 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_335, 0, x_334);
if (lean::is_scalar(x_293)) {
 x_336 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_336 = x_293;
}
lean::cnstr_set(x_336, 0, x_335);
x_7 = x_336;
x_8 = x_294;
goto lbl_9;
}
else
{
obj* x_338; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_3);
x_338 = lean::cnstr_get(x_266, 8);
lean::inc(x_338);
lean::dec(x_266);
x_341 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_341, 0, x_135);
lean::cnstr_set(x_341, 1, x_27);
x_342 = l_list_reverse___rarg(x_341);
if (lean::is_scalar(x_296)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_296;
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_338);
x_344 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_344, 0, x_343);
if (lean::is_scalar(x_293)) {
 x_345 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_345 = x_293;
}
lean::cnstr_set(x_345, 0, x_344);
x_7 = x_345;
x_8 = x_294;
goto lbl_9;
}
}
}
}
}
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_346; obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
x_346 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_348 = x_7;
} else {
 lean::inc(x_346);
 lean::dec(x_7);
 x_348 = lean::box(0);
}
if (lean::is_scalar(x_348)) {
 x_349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_349 = x_348;
}
lean::cnstr_set(x_349, 0, x_346);
x_350 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_350, 0, x_349);
x_351 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_351, 0, x_350);
lean::cnstr_set(x_351, 1, x_8);
return x_351;
}
else
{
obj* x_352; obj* x_354; 
x_352 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_354 = x_7;
} else {
 lean::inc(x_352);
 lean::dec(x_7);
 x_354 = lean::box(0);
}
if (lean::obj_tag(x_352) == 0)
{
obj* x_356; obj* x_358; obj* x_359; obj* x_360; 
lean::dec(x_354);
x_356 = lean::cnstr_get(x_352, 0);
if (lean::is_exclusive(x_352)) {
 x_358 = x_352;
} else {
 lean::inc(x_356);
 lean::dec(x_352);
 x_358 = lean::box(0);
}
if (lean::is_scalar(x_358)) {
 x_359 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_359 = x_358;
}
lean::cnstr_set(x_359, 0, x_356);
x_360 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_8);
return x_360;
}
else
{
obj* x_361; obj* x_363; obj* x_364; obj* x_365; obj* x_366; 
x_361 = lean::cnstr_get(x_352, 0);
if (lean::is_exclusive(x_352)) {
 x_363 = x_352;
} else {
 lean::inc(x_361);
 lean::dec(x_352);
 x_363 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_364 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_364 = x_354;
}
lean::cnstr_set(x_364, 0, x_361);
if (lean::is_scalar(x_363)) {
 x_365 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_365 = x_363;
}
lean::cnstr_set(x_365, 0, x_364);
x_366 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_366, 0, x_365);
lean::cnstr_set(x_366, 1, x_8);
return x_366;
}
}
}
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::box(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___boxed), 7, 5);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_7);
lean::closure_set(x_8, 3, x_4);
lean::closure_set(x_8, 4, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___rarg), 4, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::fixpoint2(x_9, x_5, x_6);
return x_10;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* _init_l_lean_run__frontend___closed__1() {
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
obj* l_lean_run__frontend(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; 
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_lean_mk__config(x_0, x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
else
{
obj* x_18; obj* x_22; obj* x_23; obj* x_25; 
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
lean::dec(x_8);
lean::inc(x_18);
x_22 = l_lean_parser_parse__header(x_18);
x_23 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_set(x_22, 1, lean::box(0));
 x_25 = x_22;
} else {
 lean::inc(x_23);
 lean::dec(x_22);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_18);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
lean::dec(x_23);
x_32 = lean::apply_2(x_2, x_29, x_5);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_25);
lean::dec(x_4);
x_37 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 x_39 = x_32;
} else {
 lean::inc(x_37);
 lean::dec(x_32);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
else
{
obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_45 = x_33;
} else {
 lean::dec(x_33);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 x_48 = x_32;
} else {
 lean::inc(x_46);
 lean::dec(x_32);
 x_48 = lean::box(0);
}
x_49 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_4);
if (lean::is_scalar(x_45)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_45;
}
lean::cnstr_set(x_51, 0, x_50);
if (lean::is_scalar(x_25)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_25;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_46);
return x_52;
}
}
else
{
obj* x_53; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_64; obj* x_65; 
x_53 = lean::cnstr_get(x_23, 0);
lean::inc(x_53);
lean::dec(x_23);
x_56 = lean::cnstr_get(x_53, 0);
x_58 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_set(x_53, 0, lean::box(0));
 lean::cnstr_set(x_53, 1, lean::box(0));
 x_60 = x_53;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
x_61 = l_list_reverse___rarg(x_58);
lean::inc(x_61);
lean::inc(x_2);
x_64 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_61, x_5);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_56);
lean::dec(x_60);
lean::dec(x_61);
lean::dec(x_18);
x_76 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_78 = x_64;
} else {
 lean::inc(x_76);
 lean::dec(x_64);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_81 = x_65;
} else {
 lean::inc(x_79);
 lean::dec(x_65);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
if (lean::is_scalar(x_78)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_78;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
return x_83;
}
else
{
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_96; obj* x_98; obj* x_99; obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_65);
x_85 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_87 = x_64;
} else {
 lean::inc(x_85);
 lean::dec(x_64);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_18, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_88, 0);
lean::inc(x_90);
lean::dec(x_88);
x_93 = lean::cnstr_get(x_90, 0);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_expander_builtin__transformers;
lean::inc(x_93);
x_98 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_98, 0, x_93);
lean::cnstr_set(x_98, 1, x_96);
x_99 = lean::cnstr_get(x_93, 2);
lean::inc(x_99);
lean::dec(x_93);
x_102 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_102, 0, x_0);
lean::cnstr_set(x_102, 1, x_1);
lean::cnstr_set(x_102, 2, x_99);
lean::inc(x_18);
x_104 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_104, 0, x_102);
lean::cnstr_set(x_104, 1, x_18);
x_105 = l_lean_run__frontend___closed__1;
lean::inc(x_104);
x_107 = l_lean_elaborator_mk__state(x_104, x_4, x_105);
x_108 = lean::box(0);
if (lean::is_scalar(x_87)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_87;
}
lean::cnstr_set(x_109, 0, x_98);
lean::cnstr_set(x_109, 1, x_108);
if (lean::is_scalar(x_60)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_60;
}
lean::cnstr_set(x_110, 0, x_18);
lean::cnstr_set(x_110, 1, x_109);
if (lean::is_scalar(x_25)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_25;
}
lean::cnstr_set(x_111, 0, x_107);
lean::cnstr_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_56);
lean::cnstr_set(x_112, 1, x_111);
x_113 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_2, x_3, x_61, x_104, x_108, x_112, x_85);
return x_113;
}
}
}
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
x_8 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4(x_0, x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
x_8 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_0, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
x_8 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(x_0, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_run__frontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
x_7 = l_lean_run__frontend(x_0, x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
obj* l___private_init_io_1__put__str___at_lean_process__file___spec__3(obj* x_0, obj* x_1) {
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
x_2 = l___private_init_io_1__put__str___at_lean_process__file___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_lean_process__file___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_io_1__put__str___at_lean_process__file___spec__3(x_0, x_1);
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
x_18 = l___private_init_io_1__put__str___at_lean_process__file___spec__3(x_17, x_14);
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
if (x_0 == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_message_to__string(x_1);
x_4 = l_io_println___at_lean_process__file___spec__1(x_3, x_2);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_31; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
x_10 = l_nat_repr(x_8);
x_11 = l_lean_process__file___lambda__1___closed__1;
x_12 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_14 = l_lean_process__file___lambda__1___closed__2;
x_15 = lean::string_append(x_12, x_14);
x_16 = lean::cnstr_get(x_6, 1);
lean::inc(x_16);
lean::dec(x_6);
x_19 = l_nat_repr(x_16);
x_20 = lean::string_append(x_15, x_19);
lean::dec(x_19);
x_22 = l_lean_process__file___lambda__1___closed__3;
x_23 = lean::string_append(x_20, x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_25 = lean::cnstr_get(x_1, 3);
lean::inc(x_25);
x_27 = l_string_quote(x_25);
x_28 = lean::cnstr_get(x_1, 4);
lean::inc(x_28);
lean::dec(x_1);
x_31 = l_string_quote(x_28);
switch (x_24) {
case 0:
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
x_32 = l_lean_process__file___lambda__1___closed__4;
x_33 = lean::string_append(x_23, x_32);
x_34 = l_lean_process__file___lambda__1___closed__5;
x_35 = lean::string_append(x_33, x_34);
x_36 = lean::string_append(x_35, x_27);
lean::dec(x_27);
x_38 = l_lean_process__file___lambda__1___closed__6;
x_39 = lean::string_append(x_36, x_38);
x_40 = lean::string_append(x_39, x_31);
lean::dec(x_31);
x_42 = l_lean_process__file___lambda__1___closed__7;
x_43 = lean::string_append(x_40, x_42);
x_44 = l_io_println___at_lean_process__file___spec__1(x_43, x_2);
lean::dec(x_43);
return x_44;
}
case 1:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
x_46 = l_lean_process__file___lambda__1___closed__8;
x_47 = lean::string_append(x_23, x_46);
x_48 = l_lean_process__file___lambda__1___closed__5;
x_49 = lean::string_append(x_47, x_48);
x_50 = lean::string_append(x_49, x_27);
lean::dec(x_27);
x_52 = l_lean_process__file___lambda__1___closed__6;
x_53 = lean::string_append(x_50, x_52);
x_54 = lean::string_append(x_53, x_31);
lean::dec(x_31);
x_56 = l_lean_process__file___lambda__1___closed__7;
x_57 = lean::string_append(x_54, x_56);
x_58 = l_io_println___at_lean_process__file___spec__1(x_57, x_2);
lean::dec(x_57);
return x_58;
}
default:
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
x_60 = l_lean_process__file___lambda__1___closed__9;
x_61 = lean::string_append(x_23, x_60);
x_62 = l_lean_process__file___lambda__1___closed__5;
x_63 = lean::string_append(x_61, x_62);
x_64 = lean::string_append(x_63, x_27);
lean::dec(x_27);
x_66 = l_lean_process__file___lambda__1___closed__6;
x_67 = lean::string_append(x_64, x_66);
x_68 = lean::string_append(x_67, x_31);
lean::dec(x_31);
x_70 = l_lean_process__file___lambda__1___closed__7;
x_71 = lean::string_append(x_68, x_70);
x_72 = l_io_println___at_lean_process__file___spec__1(x_71, x_2);
lean::dec(x_71);
return x_72;
}
}
}
}
}
obj* _init_l_lean_process__file___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_process__file___closed__2() {
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
obj* lean_process_file(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; 
x_8 = lean::box(x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = 0;
lean::inc(x_0);
x_12 = l_lean_run__frontend(x_0, x_1, x_9, x_10, x_3, x_4);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_20 = x_13;
} else {
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
x_5 = x_21;
x_6 = x_15;
goto lbl_7;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_22 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_24 = x_13;
} else {
 lean::inc(x_22);
 lean::dec(x_13);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
x_28 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_30 = x_22;
} else {
 lean::inc(x_28);
 lean::dec(x_22);
 x_30 = lean::box(0);
}
x_31 = lean::box(0);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
if (lean::is_scalar(x_24)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_24;
}
lean::cnstr_set(x_33, 0, x_32);
x_5 = x_33;
x_6 = x_25;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
if (x_2 == 0)
{
obj* x_34; obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
x_34 = lean::cnstr_get(x_5, 0);
lean::inc(x_34);
lean::dec(x_5);
x_37 = lean::box(0);
x_38 = l_lean_elaborator_notation_elaborate___closed__1;
x_39 = 2;
x_40 = l_string_iterator_extract___main___closed__1;
x_41 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_41, 0, x_0);
lean::cnstr_set(x_41, 1, x_38);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_40);
lean::cnstr_set(x_41, 4, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*5, x_39);
x_42 = x_41;
x_43 = l_lean_message_to__string(x_42);
x_44 = l_io_println___at_lean_process__file___spec__1(x_43, x_6);
lean::dec(x_43);
x_46 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_48 = x_44;
} else {
 lean::inc(x_46);
 lean::dec(x_44);
 x_48 = lean::box(0);
}
x_49 = l_lean_process__file___closed__1;
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
return x_50;
}
else
{
obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_0);
x_52 = lean::cnstr_get(x_5, 0);
lean::inc(x_52);
lean::dec(x_5);
x_55 = l_string_quote(x_52);
x_56 = l_lean_process__file___closed__2;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_59 = l_lean_process__file___lambda__1___closed__7;
x_60 = lean::string_append(x_57, x_59);
x_61 = l_io_println___at_lean_process__file___spec__1(x_60, x_6);
lean::dec(x_60);
x_63 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_65 = x_61;
} else {
 lean::inc(x_63);
 lean::dec(x_61);
 x_65 = lean::box(0);
}
x_66 = l_lean_process__file___closed__1;
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_63);
return x_67;
}
}
else
{
lean::dec(x_0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_5);
x_70 = l_lean_process__file___closed__1;
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_6);
return x_71;
}
else
{
obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_74 = x_5;
} else {
 lean::inc(x_72);
 lean::dec(x_5);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_6);
return x_76;
}
}
}
}
}
obj* l___private_init_io_1__put__str___at_lean_process__file___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_1__put__str___at_lean_process__file___spec__3(x_0, x_1);
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
obj* l_lean_process__file___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = lean_process_file(x_0, x_1, x_5, x_3, x_4);
return x_6;
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
 l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1);
 l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2);
 l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3);
 l_lean_run__frontend___closed__1 = _init_l_lean_run__frontend___closed__1();
lean::mark_persistent(l_lean_run__frontend___closed__1);
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
 l_lean_process__file___closed__2 = _init_l_lean_process__file___closed__2();
lean::mark_persistent(l_lean_process__file___closed__2);
}

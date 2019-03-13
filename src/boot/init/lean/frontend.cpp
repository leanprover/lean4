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
obj* l_io_prim_iterate__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__6;
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3(obj*, obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(obj*, obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__6;
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_parser_parse__command(obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___closed__1;
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
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
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__header(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2(obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_lean_elaborator_mk__state(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj*, obj*);
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_io_print___at_lean_process__file___spec__2(obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* x_60; obj* x_63; obj* x_66; obj* x_70; obj* x_71; 
lean::dec(x_25);
lean::dec(x_4);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_46);
x_60 = lean::cnstr_get(x_50, 1);
lean::inc(x_60);
lean::dec(x_50);
x_63 = lean::cnstr_get(x_51, 0);
lean::inc(x_63);
lean::dec(x_51);
x_66 = lean::cnstr_get(x_53, 0);
lean::inc(x_66);
lean::dec(x_53);
lean::inc(x_0);
x_70 = lean::apply_2(x_0, x_66, x_60);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_78; obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_27);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_63);
x_78 = lean::cnstr_get(x_70, 1);
lean::inc(x_78);
lean::dec(x_70);
x_81 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_83 = x_71;
} else {
 lean::inc(x_81);
 lean::dec(x_71);
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
lean::dec(x_71);
x_86 = lean::cnstr_get(x_70, 1);
lean::inc(x_86);
lean::dec(x_70);
x_89 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_0, x_1, x_86);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
if (lean::obj_tag(x_90) == 0)
{
obj* x_95; obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_63);
x_95 = lean::cnstr_get(x_89, 1);
lean::inc(x_95);
lean::dec(x_89);
x_98 = lean::cnstr_get(x_90, 0);
if (lean::is_exclusive(x_90)) {
 x_100 = x_90;
} else {
 lean::inc(x_98);
 lean::dec(x_90);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
x_7 = x_101;
x_8 = x_95;
goto lbl_9;
}
else
{
obj* x_102; 
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 x_102 = x_90;
} else {
 lean::dec(x_90);
 x_102 = lean::box(0);
}
if (x_2 == 0)
{
obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_27);
lean::dec(x_63);
x_105 = lean::cnstr_get(x_89, 1);
lean::inc(x_105);
lean::dec(x_89);
x_108 = l_list_reverse___rarg(x_3);
x_109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
if (lean::is_scalar(x_102)) {
 x_110 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_110 = x_102;
}
lean::cnstr_set(x_110, 0, x_109);
x_7 = x_110;
x_8 = x_105;
goto lbl_9;
}
else
{
obj* x_112; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_3);
x_112 = lean::cnstr_get(x_89, 1);
lean::inc(x_112);
lean::dec(x_89);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_63);
lean::cnstr_set(x_115, 1, x_27);
x_116 = l_list_reverse___rarg(x_115);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
if (lean::is_scalar(x_102)) {
 x_118 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_118 = x_102;
}
lean::cnstr_set(x_118, 0, x_117);
x_7 = x_118;
x_8 = x_112;
goto lbl_9;
}
}
}
}
else
{
obj* x_120; obj* x_123; obj* x_126; obj* x_129; obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_137; 
lean::dec(x_1);
x_120 = lean::cnstr_get(x_53, 0);
lean::inc(x_120);
lean::dec(x_53);
x_123 = lean::cnstr_get(x_50, 1);
lean::inc(x_123);
lean::dec(x_50);
x_126 = lean::cnstr_get(x_51, 0);
lean::inc(x_126);
lean::dec(x_51);
x_129 = lean::cnstr_get(x_120, 0);
x_131 = lean::cnstr_get(x_120, 1);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_set(x_120, 0, lean::box(0));
 lean::cnstr_set(x_120, 1, lean::box(0));
 x_133 = x_120;
} else {
 lean::inc(x_129);
 lean::inc(x_131);
 lean::dec(x_120);
 x_133 = lean::box(0);
}
x_134 = l_list_reverse___rarg(x_131);
lean::inc(x_0);
x_136 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(x_0, x_134, x_123);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_150; obj* x_153; obj* x_155; obj* x_156; 
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_46);
lean::dec(x_126);
lean::dec(x_133);
lean::dec(x_129);
x_150 = lean::cnstr_get(x_136, 1);
lean::inc(x_150);
lean::dec(x_136);
x_153 = lean::cnstr_get(x_137, 0);
if (lean::is_exclusive(x_137)) {
 x_155 = x_137;
} else {
 lean::inc(x_153);
 lean::dec(x_137);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
x_7 = x_156;
x_8 = x_150;
goto lbl_9;
}
else
{
obj* x_157; obj* x_158; obj* x_160; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 x_157 = x_137;
} else {
 lean::dec(x_137);
 x_157 = lean::box(0);
}
x_158 = lean::cnstr_get(x_136, 1);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_set(x_136, 1, lean::box(0));
 x_160 = x_136;
} else {
 lean::inc(x_158);
 lean::dec(x_136);
 x_160 = lean::box(0);
}
lean::inc(x_25);
lean::inc(x_126);
x_163 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_163, 0, x_126);
lean::closure_set(x_163, 1, x_25);
x_164 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2;
x_165 = l_lean_profileit__pure___rarg(x_164, x_46, x_163, x_158);
x_166 = lean::cnstr_get(x_165, 0);
lean::inc(x_166);
if (lean::obj_tag(x_166) == 0)
{
lean::dec(x_4);
lean::dec(x_46);
lean::dec(x_157);
if (x_2 == 0)
{
obj* x_173; obj* x_175; obj* x_176; obj* x_179; obj* x_180; 
lean::dec(x_27);
lean::dec(x_126);
x_173 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_set(x_165, 1, lean::box(0));
 x_175 = x_165;
} else {
 lean::inc(x_173);
 lean::dec(x_165);
 x_175 = lean::box(0);
}
x_176 = lean::cnstr_get(x_166, 0);
lean::inc(x_176);
lean::dec(x_166);
x_179 = lean::apply_2(x_0, x_176, x_173);
x_180 = lean::cnstr_get(x_179, 0);
lean::inc(x_180);
if (lean::obj_tag(x_180) == 0)
{
obj* x_190; obj* x_193; obj* x_195; obj* x_196; 
lean::dec(x_25);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_175);
lean::dec(x_160);
lean::dec(x_133);
lean::dec(x_129);
x_190 = lean::cnstr_get(x_179, 1);
lean::inc(x_190);
lean::dec(x_179);
x_193 = lean::cnstr_get(x_180, 0);
if (lean::is_exclusive(x_180)) {
 x_195 = x_180;
} else {
 lean::inc(x_193);
 lean::dec(x_180);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
x_7 = x_196;
x_8 = x_190;
goto lbl_9;
}
else
{
obj* x_197; obj* x_198; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 x_197 = x_180;
} else {
 lean::dec(x_180);
 x_197 = lean::box(0);
}
x_198 = lean::cnstr_get(x_179, 1);
if (lean::is_exclusive(x_179)) {
 lean::cnstr_release(x_179, 0);
 x_200 = x_179;
} else {
 lean::inc(x_198);
 lean::dec(x_179);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_25);
lean::cnstr_set(x_201, 1, x_3);
if (lean::is_scalar(x_175)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_175;
}
lean::cnstr_set(x_202, 0, x_22);
lean::cnstr_set(x_202, 1, x_201);
if (lean::is_scalar(x_160)) {
 x_203 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_203 = x_160;
}
lean::cnstr_set(x_203, 0, x_19);
lean::cnstr_set(x_203, 1, x_202);
if (lean::is_scalar(x_133)) {
 x_204 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_204 = x_133;
}
lean::cnstr_set(x_204, 0, x_129);
lean::cnstr_set(x_204, 1, x_203);
x_205 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_205, 0, x_204);
if (lean::is_scalar(x_197)) {
 x_206 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_206 = x_197;
}
lean::cnstr_set(x_206, 0, x_205);
x_7 = x_206;
x_8 = x_198;
goto lbl_9;
}
}
else
{
obj* x_208; obj* x_210; obj* x_211; obj* x_214; obj* x_215; 
lean::dec(x_3);
x_208 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_set(x_165, 1, lean::box(0));
 x_210 = x_165;
} else {
 lean::inc(x_208);
 lean::dec(x_165);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_166, 0);
lean::inc(x_211);
lean::dec(x_166);
x_214 = lean::apply_2(x_0, x_211, x_208);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
if (lean::obj_tag(x_215) == 0)
{
obj* x_226; obj* x_229; obj* x_231; obj* x_232; 
lean::dec(x_210);
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_160);
lean::dec(x_126);
lean::dec(x_133);
lean::dec(x_129);
x_226 = lean::cnstr_get(x_214, 1);
lean::inc(x_226);
lean::dec(x_214);
x_229 = lean::cnstr_get(x_215, 0);
if (lean::is_exclusive(x_215)) {
 x_231 = x_215;
} else {
 lean::inc(x_229);
 lean::dec(x_215);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
x_7 = x_232;
x_8 = x_226;
goto lbl_9;
}
else
{
obj* x_233; obj* x_234; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 x_233 = x_215;
} else {
 lean::dec(x_215);
 x_233 = lean::box(0);
}
x_234 = lean::cnstr_get(x_214, 1);
if (lean::is_exclusive(x_214)) {
 lean::cnstr_release(x_214, 0);
 x_236 = x_214;
} else {
 lean::inc(x_234);
 lean::dec(x_214);
 x_236 = lean::box(0);
}
x_237 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_237, 0, x_126);
lean::cnstr_set(x_237, 1, x_27);
if (lean::is_scalar(x_236)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_236;
}
lean::cnstr_set(x_238, 0, x_25);
lean::cnstr_set(x_238, 1, x_237);
if (lean::is_scalar(x_210)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_210;
}
lean::cnstr_set(x_239, 0, x_22);
lean::cnstr_set(x_239, 1, x_238);
if (lean::is_scalar(x_160)) {
 x_240 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_240 = x_160;
}
lean::cnstr_set(x_240, 0, x_19);
lean::cnstr_set(x_240, 1, x_239);
if (lean::is_scalar(x_133)) {
 x_241 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_241 = x_133;
}
lean::cnstr_set(x_241, 0, x_129);
lean::cnstr_set(x_241, 1, x_240);
x_242 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_242, 0, x_241);
if (lean::is_scalar(x_233)) {
 x_243 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_243 = x_233;
}
lean::cnstr_set(x_243, 0, x_242);
x_7 = x_243;
x_8 = x_234;
goto lbl_9;
}
}
}
else
{
obj* x_247; obj* x_249; obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_256; obj* x_258; obj* x_260; obj* x_262; obj* x_263; obj* x_265; obj* x_266; obj* x_267; obj* x_269; obj* x_271; obj* x_272; obj* x_274; 
lean::dec(x_25);
lean::dec(x_22);
lean::dec(x_133);
x_247 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_set(x_165, 1, lean::box(0));
 x_249 = x_165;
} else {
 lean::inc(x_247);
 lean::dec(x_165);
 x_249 = lean::box(0);
}
x_250 = lean::cnstr_get(x_166, 0);
if (lean::is_exclusive(x_166)) {
 lean::cnstr_set(x_166, 0, lean::box(0));
 x_252 = x_166;
} else {
 lean::inc(x_250);
 lean::dec(x_166);
 x_252 = lean::box(0);
}
lean::inc(x_250);
x_254 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_254, 0, x_4);
lean::closure_set(x_254, 1, x_19);
lean::closure_set(x_254, 2, x_250);
x_255 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3;
x_256 = l_lean_profileit__pure___rarg(x_255, x_46, x_254, x_247);
lean::dec(x_46);
x_258 = lean::cnstr_get(x_256, 0);
x_260 = lean::cnstr_get(x_256, 1);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_set(x_256, 0, lean::box(0));
 lean::cnstr_set(x_256, 1, lean::box(0));
 x_262 = x_256;
} else {
 lean::inc(x_258);
 lean::inc(x_260);
 lean::dec(x_256);
 x_262 = lean::box(0);
}
x_263 = lean::cnstr_get(x_258, 5);
lean::inc(x_263);
x_265 = l_list_reverse___rarg(x_263);
x_266 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_0, x_265, x_260);
x_267 = lean::cnstr_get(x_266, 0);
x_269 = lean::cnstr_get(x_266, 1);
if (lean::is_exclusive(x_266)) {
 lean::cnstr_set(x_266, 0, lean::box(0));
 lean::cnstr_set(x_266, 1, lean::box(0));
 x_271 = x_266;
} else {
 lean::inc(x_267);
 lean::inc(x_269);
 lean::dec(x_266);
 x_271 = lean::box(0);
}
if (lean::obj_tag(x_267) == 0)
{
obj* x_288; obj* x_290; obj* x_291; 
lean::dec(x_249);
lean::dec(x_258);
lean::dec(x_262);
lean::dec(x_252);
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_250);
lean::dec(x_271);
lean::dec(x_157);
lean::dec(x_160);
lean::dec(x_126);
lean::dec(x_129);
x_288 = lean::cnstr_get(x_267, 0);
if (lean::is_exclusive(x_267)) {
 x_290 = x_267;
} else {
 lean::inc(x_288);
 lean::dec(x_267);
 x_290 = lean::box(0);
}
if (lean::is_scalar(x_290)) {
 x_291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_291 = x_290;
}
lean::cnstr_set(x_291, 0, x_288);
x_7 = x_291;
x_8 = x_269;
goto lbl_9;
}
else
{
obj* x_293; uint8 x_294; 
lean::dec(x_267);
x_293 = l_lean_parser_module_eoi;
x_294 = l_lean_parser_syntax_is__of__kind___main(x_293, x_250);
lean::dec(x_250);
if (x_294 == 0)
{
obj* x_297; 
lean::dec(x_157);
x_297 = lean::box(0);
x_272 = x_297;
goto lbl_273;
}
else
{
obj* x_305; 
lean::dec(x_249);
lean::dec(x_258);
lean::dec(x_262);
lean::dec(x_252);
lean::dec(x_271);
lean::dec(x_160);
lean::dec(x_129);
x_305 = lean::box(0);
x_274 = x_305;
goto lbl_275;
}
}
lbl_273:
{
lean::dec(x_272);
if (x_2 == 0)
{
obj* x_309; obj* x_311; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; 
lean::dec(x_27);
lean::dec(x_126);
x_309 = lean::cnstr_get(x_258, 6);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_258, 7);
lean::inc(x_311);
if (lean::is_scalar(x_271)) {
 x_313 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_313 = x_271;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_3);
if (lean::is_scalar(x_262)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_262;
}
lean::cnstr_set(x_314, 0, x_309);
lean::cnstr_set(x_314, 1, x_313);
if (lean::is_scalar(x_249)) {
 x_315 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_315 = x_249;
}
lean::cnstr_set(x_315, 0, x_258);
lean::cnstr_set(x_315, 1, x_314);
if (lean::is_scalar(x_160)) {
 x_316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_316 = x_160;
}
lean::cnstr_set(x_316, 0, x_129);
lean::cnstr_set(x_316, 1, x_315);
x_317 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_317, 0, x_316);
if (lean::is_scalar(x_252)) {
 x_318 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_318 = x_252;
}
lean::cnstr_set(x_318, 0, x_317);
x_7 = x_318;
x_8 = x_269;
goto lbl_9;
}
else
{
obj* x_320; obj* x_322; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
lean::dec(x_3);
x_320 = lean::cnstr_get(x_258, 6);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_258, 7);
lean::inc(x_322);
x_324 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_324, 0, x_126);
lean::cnstr_set(x_324, 1, x_27);
if (lean::is_scalar(x_271)) {
 x_325 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_325 = x_271;
}
lean::cnstr_set(x_325, 0, x_322);
lean::cnstr_set(x_325, 1, x_324);
if (lean::is_scalar(x_262)) {
 x_326 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_326 = x_262;
}
lean::cnstr_set(x_326, 0, x_320);
lean::cnstr_set(x_326, 1, x_325);
if (lean::is_scalar(x_249)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_249;
}
lean::cnstr_set(x_327, 0, x_258);
lean::cnstr_set(x_327, 1, x_326);
if (lean::is_scalar(x_160)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_160;
}
lean::cnstr_set(x_328, 0, x_129);
lean::cnstr_set(x_328, 1, x_327);
x_329 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_329, 0, x_328);
if (lean::is_scalar(x_252)) {
 x_330 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_330 = x_252;
}
lean::cnstr_set(x_330, 0, x_329);
x_7 = x_330;
x_8 = x_269;
goto lbl_9;
}
}
lbl_275:
{
lean::dec(x_274);
if (x_2 == 0)
{
obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_27);
lean::dec(x_126);
x_334 = l_list_reverse___rarg(x_3);
x_335 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_335, 0, x_334);
if (lean::is_scalar(x_157)) {
 x_336 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_336 = x_157;
}
lean::cnstr_set(x_336, 0, x_335);
x_7 = x_336;
x_8 = x_269;
goto lbl_9;
}
else
{
obj* x_338; obj* x_339; obj* x_340; obj* x_341; 
lean::dec(x_3);
x_338 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_338, 0, x_126);
lean::cnstr_set(x_338, 1, x_27);
x_339 = l_list_reverse___rarg(x_338);
x_340 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_340, 0, x_339);
if (lean::is_scalar(x_157)) {
 x_341 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_341 = x_157;
}
lean::cnstr_set(x_341, 0, x_340);
x_7 = x_341;
x_8 = x_269;
goto lbl_9;
}
}
}
}
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_342; obj* x_344; obj* x_345; obj* x_346; obj* x_347; 
x_342 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_344 = x_7;
} else {
 lean::inc(x_342);
 lean::dec(x_7);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_342);
x_346 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_346, 0, x_345);
x_347 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_347, 0, x_346);
lean::cnstr_set(x_347, 1, x_8);
return x_347;
}
else
{
obj* x_348; obj* x_350; 
x_348 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_350 = x_7;
} else {
 lean::inc(x_348);
 lean::dec(x_7);
 x_350 = lean::box(0);
}
if (lean::obj_tag(x_348) == 0)
{
obj* x_352; obj* x_354; obj* x_355; obj* x_356; 
lean::dec(x_350);
x_352 = lean::cnstr_get(x_348, 0);
if (lean::is_exclusive(x_348)) {
 x_354 = x_348;
} else {
 lean::inc(x_352);
 lean::dec(x_348);
 x_354 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_355 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_355 = x_354;
}
lean::cnstr_set(x_355, 0, x_352);
x_356 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_356, 0, x_355);
lean::cnstr_set(x_356, 1, x_8);
return x_356;
}
else
{
obj* x_357; obj* x_359; obj* x_360; obj* x_361; obj* x_362; 
x_357 = lean::cnstr_get(x_348, 0);
if (lean::is_exclusive(x_348)) {
 x_359 = x_348;
} else {
 lean::inc(x_357);
 lean::dec(x_348);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_360 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_360 = x_350;
}
lean::cnstr_set(x_360, 0, x_357);
if (lean::is_scalar(x_359)) {
 x_361 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_361 = x_359;
}
lean::cnstr_set(x_361, 0, x_360);
x_362 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_362, 0, x_361);
lean::cnstr_set(x_362, 1, x_8);
return x_362;
}
}
}
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___closed__1() {
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
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_lean_expander_builtin__transformers;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_io_prim_iterate___at_lean_run__frontend___spec__6___closed__1;
lean::inc(x_6);
x_20 = l_lean_elaborator_mk__state(x_6, x_18);
lean::inc(x_7);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_7);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::box(x_1);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___boxed), 7, 5);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_4);
lean::closure_set(x_27, 2, x_26);
lean::closure_set(x_27, 3, x_7);
lean::closure_set(x_27, 4, x_6);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___rarg), 4, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::fixpoint2(x_28, x_25, x_5);
return x_29;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___boxed), 8, 0);
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
x_58 = l_lean_expander_expand__bracketed__binder___main___closed__6;
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
obj* x_60; obj* x_63; obj* x_65; obj* x_68; obj* x_71; obj* x_72; 
x_60 = lean::cnstr_get(x_34, 0);
lean::inc(x_60);
lean::dec(x_34);
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 1);
lean::inc(x_65);
lean::dec(x_60);
x_68 = l_list_reverse___rarg(x_65);
lean::inc(x_68);
lean::inc(x_2);
x_71 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_68, x_6);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_63);
lean::dec(x_68);
lean::dec(x_29);
x_80 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_82 = x_71;
} else {
 lean::inc(x_80);
 lean::dec(x_71);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_85 = x_72;
} else {
 lean::inc(x_83);
 lean::dec(x_72);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
if (lean::is_scalar(x_82)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_82;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_80);
return x_87;
}
else
{
obj* x_89; obj* x_92; obj* x_94; obj* x_97; obj* x_100; obj* x_103; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_72);
x_89 = lean::cnstr_get(x_71, 1);
lean::inc(x_89);
lean::dec(x_71);
x_92 = lean::cnstr_get(x_29, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_92, 0);
lean::inc(x_94);
lean::dec(x_92);
x_97 = lean::cnstr_get(x_94, 0);
lean::inc(x_97);
lean::dec(x_94);
x_100 = lean::cnstr_get(x_97, 2);
lean::inc(x_100);
lean::dec(x_97);
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_0);
lean::cnstr_set(x_103, 1, x_1);
lean::cnstr_set(x_103, 2, x_100);
lean::inc(x_29);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set(x_105, 1, x_29);
x_106 = lean::box(0);
x_107 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_2, x_3, x_29, x_63, x_68, x_89, x_105, x_106);
return x_107;
}
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
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
x_9 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_0, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
x_9 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___rarg(x_0, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
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
 l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1);
 l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2);
 l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3);
 l_io_prim_iterate___at_lean_run__frontend___spec__6___closed__1 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__6___closed__1();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__6___closed__1);
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

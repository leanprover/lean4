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
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_parser_parse__command(obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_string_quote(obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*);
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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj*, uint8, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_lean_elaborator_mk__state(obj*, obj*);
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
obj* x_158; obj* x_160; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_137);
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
if (x_2 == 0)
{
obj* x_172; obj* x_174; obj* x_175; obj* x_178; obj* x_179; 
lean::dec(x_27);
lean::dec(x_126);
x_172 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_set(x_165, 1, lean::box(0));
 x_174 = x_165;
} else {
 lean::inc(x_172);
 lean::dec(x_165);
 x_174 = lean::box(0);
}
x_175 = lean::cnstr_get(x_166, 0);
lean::inc(x_175);
lean::dec(x_166);
x_178 = lean::apply_2(x_0, x_175, x_172);
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
if (lean::obj_tag(x_179) == 0)
{
obj* x_189; obj* x_192; obj* x_194; obj* x_195; 
lean::dec(x_25);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_174);
lean::dec(x_160);
lean::dec(x_133);
lean::dec(x_129);
x_189 = lean::cnstr_get(x_178, 1);
lean::inc(x_189);
lean::dec(x_178);
x_192 = lean::cnstr_get(x_179, 0);
if (lean::is_exclusive(x_179)) {
 x_194 = x_179;
} else {
 lean::inc(x_192);
 lean::dec(x_179);
 x_194 = lean::box(0);
}
if (lean::is_scalar(x_194)) {
 x_195 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_195 = x_194;
}
lean::cnstr_set(x_195, 0, x_192);
x_7 = x_195;
x_8 = x_189;
goto lbl_9;
}
else
{
obj* x_196; obj* x_197; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
if (lean::is_exclusive(x_179)) {
 lean::cnstr_release(x_179, 0);
 x_196 = x_179;
} else {
 lean::dec(x_179);
 x_196 = lean::box(0);
}
x_197 = lean::cnstr_get(x_178, 1);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 x_199 = x_178;
} else {
 lean::inc(x_197);
 lean::dec(x_178);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_25);
lean::cnstr_set(x_200, 1, x_3);
if (lean::is_scalar(x_174)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_174;
}
lean::cnstr_set(x_201, 0, x_22);
lean::cnstr_set(x_201, 1, x_200);
if (lean::is_scalar(x_160)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_160;
}
lean::cnstr_set(x_202, 0, x_19);
lean::cnstr_set(x_202, 1, x_201);
if (lean::is_scalar(x_133)) {
 x_203 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_203 = x_133;
}
lean::cnstr_set(x_203, 0, x_129);
lean::cnstr_set(x_203, 1, x_202);
x_204 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_204, 0, x_203);
if (lean::is_scalar(x_196)) {
 x_205 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_205 = x_196;
}
lean::cnstr_set(x_205, 0, x_204);
x_7 = x_205;
x_8 = x_197;
goto lbl_9;
}
}
else
{
obj* x_207; obj* x_209; obj* x_210; obj* x_213; obj* x_214; 
lean::dec(x_3);
x_207 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_set(x_165, 1, lean::box(0));
 x_209 = x_165;
} else {
 lean::inc(x_207);
 lean::dec(x_165);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_166, 0);
lean::inc(x_210);
lean::dec(x_166);
x_213 = lean::apply_2(x_0, x_210, x_207);
x_214 = lean::cnstr_get(x_213, 0);
lean::inc(x_214);
if (lean::obj_tag(x_214) == 0)
{
obj* x_225; obj* x_228; obj* x_230; obj* x_231; 
lean::dec(x_209);
lean::dec(x_25);
lean::dec(x_27);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_160);
lean::dec(x_126);
lean::dec(x_133);
lean::dec(x_129);
x_225 = lean::cnstr_get(x_213, 1);
lean::inc(x_225);
lean::dec(x_213);
x_228 = lean::cnstr_get(x_214, 0);
if (lean::is_exclusive(x_214)) {
 x_230 = x_214;
} else {
 lean::inc(x_228);
 lean::dec(x_214);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_228);
x_7 = x_231;
x_8 = x_225;
goto lbl_9;
}
else
{
obj* x_232; obj* x_233; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
if (lean::is_exclusive(x_214)) {
 lean::cnstr_release(x_214, 0);
 x_232 = x_214;
} else {
 lean::dec(x_214);
 x_232 = lean::box(0);
}
x_233 = lean::cnstr_get(x_213, 1);
if (lean::is_exclusive(x_213)) {
 lean::cnstr_release(x_213, 0);
 x_235 = x_213;
} else {
 lean::inc(x_233);
 lean::dec(x_213);
 x_235 = lean::box(0);
}
x_236 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_236, 0, x_126);
lean::cnstr_set(x_236, 1, x_27);
if (lean::is_scalar(x_235)) {
 x_237 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_237 = x_235;
}
lean::cnstr_set(x_237, 0, x_25);
lean::cnstr_set(x_237, 1, x_236);
if (lean::is_scalar(x_209)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_209;
}
lean::cnstr_set(x_238, 0, x_22);
lean::cnstr_set(x_238, 1, x_237);
if (lean::is_scalar(x_160)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_160;
}
lean::cnstr_set(x_239, 0, x_19);
lean::cnstr_set(x_239, 1, x_238);
if (lean::is_scalar(x_133)) {
 x_240 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_240 = x_133;
}
lean::cnstr_set(x_240, 0, x_129);
lean::cnstr_set(x_240, 1, x_239);
x_241 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_241, 0, x_240);
if (lean::is_scalar(x_232)) {
 x_242 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_242 = x_232;
}
lean::cnstr_set(x_242, 0, x_241);
x_7 = x_242;
x_8 = x_233;
goto lbl_9;
}
}
}
else
{
obj* x_246; obj* x_248; obj* x_249; obj* x_253; obj* x_254; obj* x_255; obj* x_257; obj* x_259; obj* x_261; obj* x_262; obj* x_264; obj* x_265; obj* x_266; 
lean::dec(x_25);
lean::dec(x_22);
lean::dec(x_133);
x_246 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_set(x_165, 1, lean::box(0));
 x_248 = x_165;
} else {
 lean::inc(x_246);
 lean::dec(x_165);
 x_248 = lean::box(0);
}
x_249 = lean::cnstr_get(x_166, 0);
lean::inc(x_249);
lean::dec(x_166);
lean::inc(x_249);
x_253 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_253, 0, x_4);
lean::closure_set(x_253, 1, x_19);
lean::closure_set(x_253, 2, x_249);
x_254 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3;
x_255 = l_lean_profileit__pure___rarg(x_254, x_46, x_253, x_246);
lean::dec(x_46);
x_257 = lean::cnstr_get(x_255, 0);
x_259 = lean::cnstr_get(x_255, 1);
if (lean::is_exclusive(x_255)) {
 lean::cnstr_set(x_255, 0, lean::box(0));
 lean::cnstr_set(x_255, 1, lean::box(0));
 x_261 = x_255;
} else {
 lean::inc(x_257);
 lean::inc(x_259);
 lean::dec(x_255);
 x_261 = lean::box(0);
}
x_262 = lean::cnstr_get(x_257, 5);
lean::inc(x_262);
x_264 = l_list_reverse___rarg(x_262);
x_265 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_0, x_264, x_259);
x_266 = lean::cnstr_get(x_265, 0);
lean::inc(x_266);
if (lean::obj_tag(x_266) == 0)
{
obj* x_277; obj* x_280; obj* x_282; obj* x_283; 
lean::dec(x_248);
lean::dec(x_249);
lean::dec(x_261);
lean::dec(x_257);
lean::dec(x_27);
lean::dec(x_3);
lean::dec(x_160);
lean::dec(x_126);
lean::dec(x_129);
x_277 = lean::cnstr_get(x_265, 1);
lean::inc(x_277);
lean::dec(x_265);
x_280 = lean::cnstr_get(x_266, 0);
if (lean::is_exclusive(x_266)) {
 x_282 = x_266;
} else {
 lean::inc(x_280);
 lean::dec(x_266);
 x_282 = lean::box(0);
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_280);
x_7 = x_283;
x_8 = x_277;
goto lbl_9;
}
else
{
obj* x_284; obj* x_285; obj* x_287; obj* x_288; uint8 x_289; 
if (lean::is_exclusive(x_266)) {
 lean::cnstr_release(x_266, 0);
 x_284 = x_266;
} else {
 lean::dec(x_266);
 x_284 = lean::box(0);
}
x_285 = lean::cnstr_get(x_265, 1);
if (lean::is_exclusive(x_265)) {
 lean::cnstr_release(x_265, 0);
 lean::cnstr_set(x_265, 1, lean::box(0));
 x_287 = x_265;
} else {
 lean::inc(x_285);
 lean::dec(x_265);
 x_287 = lean::box(0);
}
x_288 = l_lean_parser_module_eoi;
x_289 = l_lean_parser_syntax_is__of__kind___main(x_288, x_249);
lean::dec(x_249);
if (x_289 == 0)
{
if (x_2 == 0)
{
obj* x_293; obj* x_295; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_27);
lean::dec(x_126);
x_293 = lean::cnstr_get(x_257, 6);
lean::inc(x_293);
x_295 = lean::cnstr_get(x_257, 7);
lean::inc(x_295);
if (lean::is_scalar(x_287)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_287;
}
lean::cnstr_set(x_297, 0, x_295);
lean::cnstr_set(x_297, 1, x_3);
if (lean::is_scalar(x_261)) {
 x_298 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_298 = x_261;
}
lean::cnstr_set(x_298, 0, x_293);
lean::cnstr_set(x_298, 1, x_297);
if (lean::is_scalar(x_248)) {
 x_299 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_299 = x_248;
}
lean::cnstr_set(x_299, 0, x_257);
lean::cnstr_set(x_299, 1, x_298);
if (lean::is_scalar(x_160)) {
 x_300 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_300 = x_160;
}
lean::cnstr_set(x_300, 0, x_129);
lean::cnstr_set(x_300, 1, x_299);
x_301 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_301, 0, x_300);
if (lean::is_scalar(x_284)) {
 x_302 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_302 = x_284;
}
lean::cnstr_set(x_302, 0, x_301);
x_7 = x_302;
x_8 = x_285;
goto lbl_9;
}
else
{
obj* x_304; obj* x_306; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; 
lean::dec(x_3);
x_304 = lean::cnstr_get(x_257, 6);
lean::inc(x_304);
x_306 = lean::cnstr_get(x_257, 7);
lean::inc(x_306);
x_308 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_308, 0, x_126);
lean::cnstr_set(x_308, 1, x_27);
if (lean::is_scalar(x_287)) {
 x_309 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_309 = x_287;
}
lean::cnstr_set(x_309, 0, x_306);
lean::cnstr_set(x_309, 1, x_308);
if (lean::is_scalar(x_261)) {
 x_310 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_310 = x_261;
}
lean::cnstr_set(x_310, 0, x_304);
lean::cnstr_set(x_310, 1, x_309);
if (lean::is_scalar(x_248)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_248;
}
lean::cnstr_set(x_311, 0, x_257);
lean::cnstr_set(x_311, 1, x_310);
if (lean::is_scalar(x_160)) {
 x_312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_312 = x_160;
}
lean::cnstr_set(x_312, 0, x_129);
lean::cnstr_set(x_312, 1, x_311);
x_313 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_313, 0, x_312);
if (lean::is_scalar(x_284)) {
 x_314 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_314 = x_284;
}
lean::cnstr_set(x_314, 0, x_313);
x_7 = x_314;
x_8 = x_285;
goto lbl_9;
}
}
else
{
lean::dec(x_248);
lean::dec(x_261);
lean::dec(x_257);
lean::dec(x_287);
lean::dec(x_160);
lean::dec(x_129);
if (x_2 == 0)
{
obj* x_323; obj* x_324; obj* x_325; 
lean::dec(x_27);
lean::dec(x_126);
x_323 = l_list_reverse___rarg(x_3);
x_324 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_324, 0, x_323);
if (lean::is_scalar(x_284)) {
 x_325 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_325 = x_284;
}
lean::cnstr_set(x_325, 0, x_324);
x_7 = x_325;
x_8 = x_285;
goto lbl_9;
}
else
{
obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
lean::dec(x_3);
x_327 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_327, 0, x_126);
lean::cnstr_set(x_327, 1, x_27);
x_328 = l_list_reverse___rarg(x_327);
x_329 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_329, 0, x_328);
if (lean::is_scalar(x_284)) {
 x_330 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_330 = x_284;
}
lean::cnstr_set(x_330, 0, x_329);
x_7 = x_330;
x_8 = x_285;
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
obj* x_331; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
x_331 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_333 = x_7;
} else {
 lean::inc(x_331);
 lean::dec(x_7);
 x_333 = lean::box(0);
}
if (lean::is_scalar(x_333)) {
 x_334 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_334 = x_333;
}
lean::cnstr_set(x_334, 0, x_331);
x_335 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_335, 0, x_334);
x_336 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_336, 0, x_335);
lean::cnstr_set(x_336, 1, x_8);
return x_336;
}
else
{
obj* x_337; obj* x_339; 
x_337 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_339 = x_7;
} else {
 lean::inc(x_337);
 lean::dec(x_7);
 x_339 = lean::box(0);
}
if (lean::obj_tag(x_337) == 0)
{
obj* x_341; obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_339);
x_341 = lean::cnstr_get(x_337, 0);
if (lean::is_exclusive(x_337)) {
 x_343 = x_337;
} else {
 lean::inc(x_341);
 lean::dec(x_337);
 x_343 = lean::box(0);
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_341);
x_345 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_345, 0, x_344);
lean::cnstr_set(x_345, 1, x_8);
return x_345;
}
else
{
obj* x_346; obj* x_348; obj* x_349; obj* x_350; obj* x_351; 
x_346 = lean::cnstr_get(x_337, 0);
if (lean::is_exclusive(x_337)) {
 x_348 = x_337;
} else {
 lean::inc(x_346);
 lean::dec(x_337);
 x_348 = lean::box(0);
}
if (lean::is_scalar(x_339)) {
 x_349 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_349 = x_339;
}
lean::cnstr_set(x_349, 0, x_346);
if (lean::is_scalar(x_348)) {
 x_350 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_350 = x_348;
}
lean::cnstr_set(x_350, 0, x_349);
x_351 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_351, 0, x_350);
lean::cnstr_set(x_351, 1, x_8);
return x_351;
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
obj* l_lean_run__frontend(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_lean_mk__config(x_0, x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_4);
return x_15;
}
else
{
obj* x_16; obj* x_20; obj* x_21; obj* x_23; 
x_16 = lean::cnstr_get(x_7, 0);
lean::inc(x_16);
lean::dec(x_7);
lean::inc(x_16);
x_20 = l_lean_parser_parse__header(x_16);
x_21 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_set(x_20, 1, lean::box(0));
 x_23 = x_20;
} else {
 lean::inc(x_21);
 lean::dec(x_20);
 x_23 = lean::box(0);
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_28; obj* x_31; obj* x_32; 
lean::dec(x_23);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_16);
x_28 = lean::cnstr_get(x_21, 0);
lean::inc(x_28);
lean::dec(x_21);
x_31 = lean::apply_2(x_2, x_28, x_4);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
x_34 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_36 = x_31;
} else {
 lean::inc(x_34);
 lean::dec(x_31);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_39 = x_32;
} else {
 lean::inc(x_37);
 lean::dec(x_32);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_34);
return x_41;
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_32);
x_43 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_45 = x_31;
} else {
 lean::inc(x_43);
 lean::dec(x_31);
 x_45 = lean::box(0);
}
x_46 = l_lean_expander_expand__bracketed__binder___main___closed__4;
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_43);
return x_47;
}
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_59; obj* x_60; 
x_48 = lean::cnstr_get(x_21, 0);
lean::inc(x_48);
lean::dec(x_21);
x_51 = lean::cnstr_get(x_48, 0);
x_53 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 lean::cnstr_set(x_48, 1, lean::box(0));
 x_55 = x_48;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_48);
 x_55 = lean::box(0);
}
x_56 = l_list_reverse___rarg(x_53);
lean::inc(x_56);
lean::inc(x_2);
x_59 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_56, x_4);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_23);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_56);
lean::dec(x_55);
lean::dec(x_16);
lean::dec(x_51);
x_70 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_72 = x_59;
} else {
 lean::inc(x_70);
 lean::dec(x_59);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_75 = x_60;
} else {
 lean::inc(x_73);
 lean::dec(x_60);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
if (lean::is_scalar(x_72)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_72;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_70);
return x_77;
}
else
{
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_87; obj* x_90; obj* x_92; obj* x_93; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_60);
x_79 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_81 = x_59;
} else {
 lean::inc(x_79);
 lean::dec(x_59);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_16, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_82, 0);
lean::inc(x_84);
lean::dec(x_82);
x_87 = lean::cnstr_get(x_84, 0);
lean::inc(x_87);
lean::dec(x_84);
x_90 = l_lean_expander_builtin__transformers;
lean::inc(x_87);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_87);
lean::cnstr_set(x_92, 1, x_90);
x_93 = lean::cnstr_get(x_87, 2);
lean::inc(x_93);
lean::dec(x_87);
x_96 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_96, 0, x_0);
lean::cnstr_set(x_96, 1, x_1);
lean::cnstr_set(x_96, 2, x_93);
lean::inc(x_16);
x_98 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set(x_98, 1, x_16);
x_99 = l_lean_run__frontend___closed__1;
lean::inc(x_98);
x_101 = l_lean_elaborator_mk__state(x_98, x_99);
x_102 = lean::box(0);
if (lean::is_scalar(x_81)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_81;
}
lean::cnstr_set(x_103, 0, x_92);
lean::cnstr_set(x_103, 1, x_102);
if (lean::is_scalar(x_55)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_55;
}
lean::cnstr_set(x_104, 0, x_16);
lean::cnstr_set(x_104, 1, x_103);
if (lean::is_scalar(x_23)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_23;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set(x_105, 1, x_104);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_51);
lean::cnstr_set(x_106, 1, x_105);
x_107 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_2, x_3, x_56, x_98, x_102, x_106, x_79);
return x_107;
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
obj* l_lean_run__frontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
x_6 = l_lean_run__frontend(x_0, x_1, x_2, x_5, x_4);
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
obj* x_4; obj* x_5; uint8 x_6; obj* x_8; obj* x_9; 
x_4 = lean::box(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = 0;
lean::inc(x_0);
x_8 = l_lean_run__frontend(x_0, x_1, x_5, x_6, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
if (x_2 == 0)
{
obj* x_11; obj* x_14; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::box(0);
x_18 = l_lean_elaborator_notation_elaborate___closed__1;
x_19 = 2;
x_20 = l_string_iterator_extract___main___closed__1;
x_21 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_20);
lean::cnstr_set(x_21, 4, x_14);
lean::cnstr_set_scalar(x_21, sizeof(void*)*5, x_19);
x_22 = x_21;
x_23 = l_lean_message_to__string(x_22);
x_24 = l_io_println___at_lean_process__file___spec__1(x_23, x_11);
lean::dec(x_23);
x_26 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_28 = x_24;
} else {
 lean::inc(x_26);
 lean::dec(x_24);
 x_28 = lean::box(0);
}
x_29 = lean::box(x_6);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_0);
x_32 = lean::cnstr_get(x_8, 1);
lean::inc(x_32);
lean::dec(x_8);
x_35 = lean::cnstr_get(x_9, 0);
lean::inc(x_35);
lean::dec(x_9);
x_38 = l_string_quote(x_35);
x_39 = l_lean_process__file___closed__1;
x_40 = lean::string_append(x_39, x_38);
lean::dec(x_38);
x_42 = l_lean_process__file___lambda__1___closed__7;
x_43 = lean::string_append(x_40, x_42);
x_44 = l_io_println___at_lean_process__file___spec__1(x_43, x_32);
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
x_49 = lean::box(x_6);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
return x_50;
}
}
else
{
obj* x_53; obj* x_55; uint8 x_56; obj* x_57; obj* x_58; 
lean::dec(x_9);
lean::dec(x_0);
x_53 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_55 = x_8;
} else {
 lean::inc(x_53);
 lean::dec(x_8);
 x_55 = lean::box(0);
}
x_56 = 1;
x_57 = lean::box(x_56);
if (lean::is_scalar(x_55)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_55;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_53);
return x_58;
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
}

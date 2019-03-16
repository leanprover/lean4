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
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_io_1__put__str___at_lean_process__file___spec__3(obj*, obj*);
obj* l_io_prim_iterate__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_process__file___lambda__1___closed__6;
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__2;
obj* l_lean_parser_parse__command(obj*, obj*);
obj* l_string_quote(obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__3(obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__3;
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_process__file___closed__1;
obj* l_lean_run__frontend___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_lean_process__file___closed__2;
extern obj* l_lean_parser_module_eoi;
obj* l_io_println___at_lean_process__file___spec__1___boxed(obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_io_print___at_lean_process__file___spec__2___boxed(obj*, obj*);
obj* l_io_println___at_lean_process__file___spec__1(obj*, obj*);
extern obj* l_lean_options_mk;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l___private_init_io_1__put__str___at_lean_process__file___spec__3___boxed(obj*, obj*);
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__2(obj*, obj*, obj*);
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5(obj*, uint8, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parse__header(obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_lean_elaborator_mk__state(obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__1;
obj* l_io_print___at_lean_process__file___spec__2(obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
} else {
 lean::inc(x_20);
 lean::dec(x_15);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_25 = x_16;
} else {
 lean::inc(x_23);
 lean::dec(x_16);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
if (lean::is_scalar(x_22)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_22;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_20);
return x_27;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_16);
x_29 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_31 = x_15;
} else {
 lean::inc(x_29);
 lean::dec(x_15);
 x_31 = lean::box(0);
}
x_32 = lean::box(0);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
x_1 = x_11;
x_2 = x_33;
goto _start;
}
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_0);
lean::dec(x_11);
x_37 = lean::cnstr_get(x_15, 0);
x_39 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_41 = x_15;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_15);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_37);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::apply_2(x_0, x_9, x_2);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
x_19 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
x_1 = x_11;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_11);
x_24 = lean::cnstr_get(x_15, 0);
x_26 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_28 = x_15;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_15);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__command(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_expand(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_process__command(x_0, x_1, x_2);
return x_4;
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_35; obj* x_38; obj* x_40; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_16 = lean::cnstr_get(x_7, 0);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_release(x_9, 1);
 x_21 = x_9;
} else {
 lean::inc(x_19);
 lean::dec(x_9);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_11, 0);
x_24 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 x_26 = x_11;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_11);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 0);
lean::inc(x_29);
lean::dec(x_27);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::cnstr_get(x_32, 2);
lean::inc(x_35);
lean::dec(x_32);
x_38 = lean::cnstr_get(x_13, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
x_43 = l_lean_file__map_to__position(x_35, x_40);
lean::inc(x_19);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__1___boxed), 3, 2);
lean::closure_set(x_45, 0, x_19);
lean::closure_set(x_45, 1, x_13);
x_46 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__1;
x_47 = l_lean_profileit__pure___rarg(x_46, x_43, x_45, x_6);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
x_48 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_48, 0);
x_55 = lean::cnstr_get(x_48, 1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 lean::cnstr_set(x_48, 1, lean::box(0));
 x_57 = x_48;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_48);
 x_57 = lean::box(0);
}
x_58 = lean::box(0);
if (lean::is_scalar(x_52)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_52;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_50);
if (lean::obj_tag(x_55) == 0)
{
obj* x_66; obj* x_68; obj* x_70; 
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_43);
lean::dec(x_26);
x_66 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_set(x_55, 0, lean::box(0));
 x_68 = x_55;
} else {
 lean::inc(x_66);
 lean::dec(x_55);
 x_68 = lean::box(0);
}
lean::inc(x_0);
x_70 = lean::apply_2(x_0, x_66, x_59);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
x_71 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_73 = x_70;
} else {
 lean::inc(x_71);
 lean::dec(x_70);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_58);
lean::cnstr_set(x_74, 1, x_71);
x_75 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_0, x_1, x_74);
if (lean::obj_tag(x_75) == 0)
{
if (x_2 == 0)
{
obj* x_78; obj* x_80; obj* x_81; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_24);
lean::dec(x_53);
x_78 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_80 = x_75;
} else {
 lean::inc(x_78);
 lean::dec(x_75);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_16, 8);
lean::inc(x_81);
lean::dec(x_16);
x_84 = l_list_reverse___rarg(x_3);
if (lean::is_scalar(x_57)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_57;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_81);
if (lean::is_scalar(x_68)) {
 x_86 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_86 = x_68;
 lean::cnstr_set_tag(x_68, 1);
}
lean::cnstr_set(x_86, 0, x_85);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
if (lean::is_scalar(x_80)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_80;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_78);
return x_88;
}
else
{
obj* x_90; obj* x_92; obj* x_93; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_3);
x_90 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_92 = x_75;
} else {
 lean::inc(x_90);
 lean::dec(x_75);
 x_92 = lean::box(0);
}
x_93 = lean::cnstr_get(x_16, 8);
lean::inc(x_93);
lean::dec(x_16);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_53);
lean::cnstr_set(x_96, 1, x_24);
x_97 = l_list_reverse___rarg(x_96);
if (lean::is_scalar(x_57)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_57;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_93);
if (lean::is_scalar(x_68)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_68;
 lean::cnstr_set_tag(x_68, 1);
}
lean::cnstr_set(x_99, 0, x_98);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
if (lean::is_scalar(x_92)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_92;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_90);
return x_101;
}
}
else
{
obj* x_108; obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_57);
lean::dec(x_68);
lean::dec(x_53);
x_108 = lean::cnstr_get(x_75, 0);
x_110 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 x_112 = x_75;
} else {
 lean::inc(x_108);
 lean::inc(x_110);
 lean::dec(x_75);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_108);
lean::cnstr_set(x_113, 1, x_110);
return x_113;
}
}
else
{
obj* x_122; obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_57);
lean::dec(x_68);
lean::dec(x_53);
x_122 = lean::cnstr_get(x_70, 0);
x_124 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 x_126 = x_70;
} else {
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_70);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_122);
lean::cnstr_set(x_127, 1, x_124);
return x_127;
}
}
else
{
obj* x_129; obj* x_132; obj* x_134; obj* x_136; obj* x_137; obj* x_139; 
lean::dec(x_1);
x_129 = lean::cnstr_get(x_55, 0);
lean::inc(x_129);
lean::dec(x_55);
x_132 = lean::cnstr_get(x_129, 0);
x_134 = lean::cnstr_get(x_129, 1);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_set(x_129, 0, lean::box(0));
 lean::cnstr_set(x_129, 1, lean::box(0));
 x_136 = x_129;
} else {
 lean::inc(x_132);
 lean::inc(x_134);
 lean::dec(x_129);
 x_136 = lean::box(0);
}
x_137 = l_list_reverse___rarg(x_134);
lean::inc(x_0);
x_139 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(x_0, x_137, x_59);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_142; obj* x_143; obj* x_146; obj* x_147; obj* x_148; 
x_140 = lean::cnstr_get(x_139, 1);
if (lean::is_exclusive(x_139)) {
 lean::cnstr_release(x_139, 0);
 x_142 = x_139;
} else {
 lean::inc(x_140);
 lean::dec(x_139);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_58);
lean::cnstr_set(x_143, 1, x_140);
lean::inc(x_22);
lean::inc(x_53);
x_146 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__2___boxed), 3, 2);
lean::closure_set(x_146, 0, x_53);
lean::closure_set(x_146, 1, x_22);
x_147 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__2;
x_148 = l_lean_profileit__pure___rarg(x_147, x_43, x_146, x_143);
if (lean::obj_tag(x_148) == 0)
{
obj* x_149; obj* x_151; obj* x_153; obj* x_154; 
x_149 = lean::cnstr_get(x_148, 0);
x_151 = lean::cnstr_get(x_148, 1);
if (lean::is_exclusive(x_148)) {
 x_153 = x_148;
} else {
 lean::inc(x_149);
 lean::inc(x_151);
 lean::dec(x_148);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_58);
lean::cnstr_set(x_154, 1, x_151);
if (lean::obj_tag(x_149) == 0)
{
lean::dec(x_4);
lean::dec(x_43);
if (x_2 == 0)
{
obj* x_159; obj* x_162; 
lean::dec(x_24);
lean::dec(x_53);
x_159 = lean::cnstr_get(x_149, 0);
lean::inc(x_159);
lean::dec(x_149);
x_162 = lean::apply_2(x_0, x_159, x_154);
if (lean::obj_tag(x_162) == 0)
{
obj* x_163; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_163 = lean::cnstr_get(x_162, 1);
if (lean::is_exclusive(x_162)) {
 lean::cnstr_release(x_162, 0);
 x_165 = x_162;
} else {
 lean::inc(x_163);
 lean::dec(x_162);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_166 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_166 = x_136;
}
lean::cnstr_set(x_166, 0, x_22);
lean::cnstr_set(x_166, 1, x_3);
if (lean::is_scalar(x_57)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_57;
}
lean::cnstr_set(x_167, 0, x_19);
lean::cnstr_set(x_167, 1, x_166);
if (lean::is_scalar(x_26)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_26;
}
lean::cnstr_set(x_168, 0, x_16);
lean::cnstr_set(x_168, 1, x_167);
if (lean::is_scalar(x_21)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_21;
}
lean::cnstr_set(x_169, 0, x_132);
lean::cnstr_set(x_169, 1, x_168);
x_170 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_170, 0, x_169);
if (lean::is_scalar(x_165)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_165;
}
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_163);
return x_171;
}
else
{
obj* x_181; obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_22);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_132);
lean::dec(x_136);
x_181 = lean::cnstr_get(x_162, 0);
x_183 = lean::cnstr_get(x_162, 1);
if (lean::is_exclusive(x_162)) {
 x_185 = x_162;
} else {
 lean::inc(x_181);
 lean::inc(x_183);
 lean::dec(x_162);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_181);
lean::cnstr_set(x_186, 1, x_183);
return x_186;
}
}
else
{
obj* x_188; obj* x_191; 
lean::dec(x_3);
x_188 = lean::cnstr_get(x_149, 0);
lean::inc(x_188);
lean::dec(x_149);
x_191 = lean::apply_2(x_0, x_188, x_154);
if (lean::obj_tag(x_191) == 0)
{
obj* x_192; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
x_192 = lean::cnstr_get(x_191, 1);
if (lean::is_exclusive(x_191)) {
 lean::cnstr_release(x_191, 0);
 x_194 = x_191;
} else {
 lean::inc(x_192);
 lean::dec(x_191);
 x_194 = lean::box(0);
}
x_195 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_195, 0, x_53);
lean::cnstr_set(x_195, 1, x_24);
if (lean::is_scalar(x_136)) {
 x_196 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_196 = x_136;
}
lean::cnstr_set(x_196, 0, x_22);
lean::cnstr_set(x_196, 1, x_195);
if (lean::is_scalar(x_57)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_57;
}
lean::cnstr_set(x_197, 0, x_19);
lean::cnstr_set(x_197, 1, x_196);
if (lean::is_scalar(x_26)) {
 x_198 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_198 = x_26;
}
lean::cnstr_set(x_198, 0, x_16);
lean::cnstr_set(x_198, 1, x_197);
if (lean::is_scalar(x_21)) {
 x_199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_199 = x_21;
}
lean::cnstr_set(x_199, 0, x_132);
lean::cnstr_set(x_199, 1, x_198);
x_200 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_200, 0, x_199);
if (lean::is_scalar(x_194)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_194;
}
lean::cnstr_set(x_201, 0, x_200);
lean::cnstr_set(x_201, 1, x_192);
return x_201;
}
else
{
obj* x_212; obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_136);
x_212 = lean::cnstr_get(x_191, 0);
x_214 = lean::cnstr_get(x_191, 1);
if (lean::is_exclusive(x_191)) {
 x_216 = x_191;
} else {
 lean::inc(x_212);
 lean::inc(x_214);
 lean::dec(x_191);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_212);
lean::cnstr_set(x_217, 1, x_214);
return x_217;
}
}
}
else
{
obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_226; 
lean::dec(x_22);
lean::dec(x_19);
x_220 = lean::cnstr_get(x_149, 0);
if (lean::is_exclusive(x_149)) {
 lean::cnstr_set(x_149, 0, lean::box(0));
 x_222 = x_149;
} else {
 lean::inc(x_220);
 lean::dec(x_149);
 x_222 = lean::box(0);
}
lean::inc(x_220);
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__3___boxed), 4, 3);
lean::closure_set(x_224, 0, x_4);
lean::closure_set(x_224, 1, x_16);
lean::closure_set(x_224, 2, x_220);
x_225 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__3;
x_226 = l_lean_profileit__pure___rarg(x_225, x_43, x_224, x_154);
lean::dec(x_43);
if (lean::obj_tag(x_226) == 0)
{
obj* x_228; obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_236; obj* x_237; 
x_228 = lean::cnstr_get(x_226, 0);
x_230 = lean::cnstr_get(x_226, 1);
if (lean::is_exclusive(x_226)) {
 x_232 = x_226;
} else {
 lean::inc(x_228);
 lean::inc(x_230);
 lean::dec(x_226);
 x_232 = lean::box(0);
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_58);
lean::cnstr_set(x_233, 1, x_230);
x_234 = lean::cnstr_get(x_228, 5);
lean::inc(x_234);
x_236 = l_list_reverse___rarg(x_234);
x_237 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_0, x_236, x_233);
if (lean::obj_tag(x_237) == 0)
{
obj* x_238; obj* x_240; obj* x_241; uint8 x_242; 
x_238 = lean::cnstr_get(x_237, 1);
if (lean::is_exclusive(x_237)) {
 lean::cnstr_release(x_237, 0);
 lean::cnstr_set(x_237, 1, lean::box(0));
 x_240 = x_237;
} else {
 lean::inc(x_238);
 lean::dec(x_237);
 x_240 = lean::box(0);
}
x_241 = l_lean_parser_module_eoi;
x_242 = l_lean_parser_syntax_is__of__kind___main(x_241, x_220);
lean::dec(x_220);
if (x_242 == 0)
{
lean::dec(x_222);
if (x_2 == 0)
{
obj* x_247; obj* x_249; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
lean::dec(x_24);
lean::dec(x_53);
x_247 = lean::cnstr_get(x_228, 6);
lean::inc(x_247);
x_249 = lean::cnstr_get(x_228, 7);
lean::inc(x_249);
if (lean::is_scalar(x_136)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_136;
}
lean::cnstr_set(x_251, 0, x_249);
lean::cnstr_set(x_251, 1, x_3);
if (lean::is_scalar(x_57)) {
 x_252 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_252 = x_57;
}
lean::cnstr_set(x_252, 0, x_247);
lean::cnstr_set(x_252, 1, x_251);
if (lean::is_scalar(x_26)) {
 x_253 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_253 = x_26;
}
lean::cnstr_set(x_253, 0, x_228);
lean::cnstr_set(x_253, 1, x_252);
if (lean::is_scalar(x_21)) {
 x_254 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_254 = x_21;
}
lean::cnstr_set(x_254, 0, x_132);
lean::cnstr_set(x_254, 1, x_253);
x_255 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_255, 0, x_254);
if (lean::is_scalar(x_240)) {
 x_256 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_256 = x_240;
}
lean::cnstr_set(x_256, 0, x_255);
lean::cnstr_set(x_256, 1, x_238);
return x_256;
}
else
{
obj* x_258; obj* x_260; obj* x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; 
lean::dec(x_3);
x_258 = lean::cnstr_get(x_228, 6);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_228, 7);
lean::inc(x_260);
x_262 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_262, 0, x_53);
lean::cnstr_set(x_262, 1, x_24);
if (lean::is_scalar(x_136)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_136;
}
lean::cnstr_set(x_263, 0, x_260);
lean::cnstr_set(x_263, 1, x_262);
if (lean::is_scalar(x_57)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_57;
}
lean::cnstr_set(x_264, 0, x_258);
lean::cnstr_set(x_264, 1, x_263);
if (lean::is_scalar(x_26)) {
 x_265 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_265 = x_26;
}
lean::cnstr_set(x_265, 0, x_228);
lean::cnstr_set(x_265, 1, x_264);
if (lean::is_scalar(x_21)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_21;
}
lean::cnstr_set(x_266, 0, x_132);
lean::cnstr_set(x_266, 1, x_265);
x_267 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_267, 0, x_266);
if (lean::is_scalar(x_240)) {
 x_268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_268 = x_240;
}
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_238);
return x_268;
}
}
else
{
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_132);
if (x_2 == 0)
{
obj* x_275; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
lean::dec(x_24);
lean::dec(x_53);
x_275 = lean::cnstr_get(x_228, 8);
lean::inc(x_275);
lean::dec(x_228);
x_278 = l_list_reverse___rarg(x_3);
if (lean::is_scalar(x_136)) {
 x_279 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_279 = x_136;
}
lean::cnstr_set(x_279, 0, x_278);
lean::cnstr_set(x_279, 1, x_275);
if (lean::is_scalar(x_222)) {
 x_280 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_280 = x_222;
}
lean::cnstr_set(x_280, 0, x_279);
x_281 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_281, 0, x_280);
if (lean::is_scalar(x_240)) {
 x_282 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_282 = x_240;
}
lean::cnstr_set(x_282, 0, x_281);
lean::cnstr_set(x_282, 1, x_238);
return x_282;
}
else
{
obj* x_284; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; 
lean::dec(x_3);
x_284 = lean::cnstr_get(x_228, 8);
lean::inc(x_284);
lean::dec(x_228);
x_287 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_287, 0, x_53);
lean::cnstr_set(x_287, 1, x_24);
x_288 = l_list_reverse___rarg(x_287);
if (lean::is_scalar(x_136)) {
 x_289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_289 = x_136;
}
lean::cnstr_set(x_289, 0, x_288);
lean::cnstr_set(x_289, 1, x_284);
if (lean::is_scalar(x_222)) {
 x_290 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_290 = x_222;
}
lean::cnstr_set(x_290, 0, x_289);
x_291 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_291, 0, x_290);
if (lean::is_scalar(x_240)) {
 x_292 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_292 = x_240;
}
lean::cnstr_set(x_292, 0, x_291);
lean::cnstr_set(x_292, 1, x_238);
return x_292;
}
}
}
else
{
obj* x_304; obj* x_306; obj* x_308; obj* x_309; 
lean::dec(x_220);
lean::dec(x_222);
lean::dec(x_24);
lean::dec(x_3);
lean::dec(x_21);
lean::dec(x_228);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_136);
x_304 = lean::cnstr_get(x_237, 0);
x_306 = lean::cnstr_get(x_237, 1);
if (lean::is_exclusive(x_237)) {
 x_308 = x_237;
} else {
 lean::inc(x_304);
 lean::inc(x_306);
 lean::dec(x_237);
 x_308 = lean::box(0);
}
if (lean::is_scalar(x_308)) {
 x_309 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_309 = x_308;
}
lean::cnstr_set(x_309, 0, x_304);
lean::cnstr_set(x_309, 1, x_306);
return x_309;
}
}
else
{
obj* x_321; obj* x_323; obj* x_325; obj* x_326; 
lean::dec(x_220);
lean::dec(x_222);
lean::dec(x_24);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_136);
x_321 = lean::cnstr_get(x_226, 0);
x_323 = lean::cnstr_get(x_226, 1);
if (lean::is_exclusive(x_226)) {
 x_325 = x_226;
} else {
 lean::inc(x_321);
 lean::inc(x_323);
 lean::dec(x_226);
 x_325 = lean::box(0);
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_321);
lean::cnstr_set(x_326, 1, x_323);
return x_326;
}
}
}
else
{
obj* x_341; obj* x_343; obj* x_345; obj* x_346; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_43);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_136);
x_341 = lean::cnstr_get(x_148, 0);
x_343 = lean::cnstr_get(x_148, 1);
if (lean::is_exclusive(x_148)) {
 x_345 = x_148;
} else {
 lean::inc(x_341);
 lean::inc(x_343);
 lean::dec(x_148);
 x_345 = lean::box(0);
}
if (lean::is_scalar(x_345)) {
 x_346 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_346 = x_345;
}
lean::cnstr_set(x_346, 0, x_341);
lean::cnstr_set(x_346, 1, x_343);
return x_346;
}
}
else
{
obj* x_361; obj* x_363; obj* x_365; obj* x_366; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_43);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_136);
x_361 = lean::cnstr_get(x_139, 0);
x_363 = lean::cnstr_get(x_139, 1);
if (lean::is_exclusive(x_139)) {
 x_365 = x_139;
} else {
 lean::inc(x_361);
 lean::inc(x_363);
 lean::dec(x_139);
 x_365 = lean::box(0);
}
if (lean::is_scalar(x_365)) {
 x_366 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_366 = x_365;
}
lean::cnstr_set(x_366, 0, x_361);
lean::cnstr_set(x_366, 1, x_363);
return x_366;
}
}
}
else
{
obj* x_378; obj* x_380; obj* x_382; obj* x_383; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_43);
lean::dec(x_26);
x_378 = lean::cnstr_get(x_47, 0);
x_380 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_382 = x_47;
} else {
 lean::inc(x_378);
 lean::inc(x_380);
 lean::dec(x_47);
 x_382 = lean::box(0);
}
if (lean::is_scalar(x_382)) {
 x_383 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_383 = x_382;
}
lean::cnstr_set(x_383, 0, x_378);
lean::cnstr_set(x_383, 1, x_380);
return x_383;
}
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::box(x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___boxed), 7, 5);
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
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
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
x_16 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_18 = x_5;
} else {
 lean::inc(x_16);
 lean::dec(x_5);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_13);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
lean::dec(x_8);
x_24 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
lean::inc(x_21);
x_28 = l_lean_parser_parse__header(x_21);
x_29 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_set(x_28, 1, lean::box(0));
 x_31 = x_28;
} else {
 lean::inc(x_29);
 lean::dec(x_28);
 x_31 = lean::box(0);
}
x_32 = lean::box(0);
if (lean::is_scalar(x_26)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_26;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
if (lean::obj_tag(x_29) == 0)
{
obj* x_37; obj* x_40; 
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_0);
x_37 = lean::cnstr_get(x_29, 0);
lean::inc(x_37);
lean::dec(x_29);
x_40 = lean::apply_2(x_2, x_37, x_33);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; 
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_4);
lean::dec(x_31);
x_45 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_47 = x_40;
} else {
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
x_48 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_50 = x_41;
} else {
 lean::inc(x_48);
 lean::dec(x_41);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
if (lean::is_scalar(x_47)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_47;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_45);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_53 = x_41;
} else {
 lean::dec(x_41);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_56 = x_40;
} else {
 lean::inc(x_54);
 lean::dec(x_40);
 x_56 = lean::box(0);
}
x_57 = lean::box(0);
if (lean::is_scalar(x_31)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_31;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_4);
if (lean::is_scalar(x_53)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_53;
}
lean::cnstr_set(x_59, 0, x_58);
if (lean::is_scalar(x_56)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_56;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_54);
return x_60;
}
}
else
{
obj* x_63; obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_4);
lean::dec(x_31);
x_63 = lean::cnstr_get(x_40, 0);
x_65 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 x_67 = x_40;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_40);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set(x_68, 1, x_65);
return x_68;
}
}
else
{
obj* x_69; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_80; 
x_69 = lean::cnstr_get(x_29, 0);
lean::inc(x_69);
lean::dec(x_29);
x_72 = lean::cnstr_get(x_69, 0);
x_74 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_set(x_69, 0, lean::box(0));
 lean::cnstr_set(x_69, 1, lean::box(0));
 x_76 = x_69;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_69);
 x_76 = lean::box(0);
}
x_77 = l_list_reverse___rarg(x_74);
lean::inc(x_77);
lean::inc(x_2);
x_80 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_77, x_33);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; 
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
if (lean::obj_tag(x_81) == 0)
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_72);
lean::dec(x_76);
lean::dec(x_77);
x_92 = lean::cnstr_get(x_80, 1);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_94 = x_80;
} else {
 lean::inc(x_92);
 lean::dec(x_80);
 x_94 = lean::box(0);
}
x_95 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_97 = x_81;
} else {
 lean::inc(x_95);
 lean::dec(x_81);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
if (lean::is_scalar(x_94)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_94;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_92);
return x_99;
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_107; obj* x_110; obj* x_113; obj* x_115; obj* x_116; obj* x_119; obj* x_121; obj* x_122; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_81);
x_101 = lean::cnstr_get(x_80, 1);
if (lean::is_exclusive(x_80)) {
 lean::cnstr_release(x_80, 0);
 x_103 = x_80;
} else {
 lean::inc(x_101);
 lean::dec(x_80);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_32);
lean::cnstr_set(x_104, 1, x_101);
x_105 = lean::cnstr_get(x_21, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_105, 0);
lean::inc(x_107);
lean::dec(x_105);
x_110 = lean::cnstr_get(x_107, 0);
lean::inc(x_110);
lean::dec(x_107);
x_113 = l_lean_expander_builtin__transformers;
lean::inc(x_110);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_110);
lean::cnstr_set(x_115, 1, x_113);
x_116 = lean::cnstr_get(x_110, 2);
lean::inc(x_116);
lean::dec(x_110);
x_119 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_119, 0, x_0);
lean::cnstr_set(x_119, 1, x_1);
lean::cnstr_set(x_119, 2, x_116);
lean::inc(x_21);
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_21);
x_122 = l_lean_run__frontend___closed__1;
lean::inc(x_121);
x_124 = l_lean_elaborator_mk__state(x_121, x_4, x_122);
x_125 = lean::box(0);
if (lean::is_scalar(x_76)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_76;
}
lean::cnstr_set(x_126, 0, x_115);
lean::cnstr_set(x_126, 1, x_125);
if (lean::is_scalar(x_31)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_31;
}
lean::cnstr_set(x_127, 0, x_21);
lean::cnstr_set(x_127, 1, x_126);
x_128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_128, 0, x_124);
lean::cnstr_set(x_128, 1, x_127);
x_129 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_129, 0, x_72);
lean::cnstr_set(x_129, 1, x_128);
x_130 = l_io_prim_iterate___at_lean_run__frontend___spec__5(x_2, x_3, x_77, x_121, x_125, x_129, x_104);
return x_130;
}
}
else
{
obj* x_140; obj* x_142; obj* x_144; obj* x_145; 
lean::dec(x_21);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_72);
lean::dec(x_76);
lean::dec(x_77);
x_140 = lean::cnstr_get(x_80, 0);
x_142 = lean::cnstr_get(x_80, 1);
if (lean::is_exclusive(x_80)) {
 x_144 = x_80;
} else {
 lean::inc(x_140);
 lean::inc(x_142);
 lean::dec(x_80);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_140);
lean::cnstr_set(x_145, 1, x_142);
return x_145;
}
}
}
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
x_8 = l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4(x_0, x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_io_prim_iterate___at_lean_run__frontend___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_1);
x_8 = l_io_prim_iterate___at_lean_run__frontend___spec__5(x_0, x_7, x_2, x_3, x_4, x_5, x_6);
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
obj* x_2; 
x_2 = lean_io_prim_put_str(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_2, 0);
x_12 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_14 = x_2;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_2);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
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
obj* x_2; 
x_2 = l___private_init_io_1__put__str___at_lean_process__file___spec__3(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
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
obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_3);
x_14 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_16 = x_2;
} else {
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
x_17 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_16;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
x_19 = l_lean_format_be___main___closed__1;
x_20 = l___private_init_io_1__put__str___at_lean_process__file___spec__3(x_19, x_18);
return x_20;
}
}
else
{
obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_25 = x_2;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_2);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_21);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; uint8 x_13; obj* x_15; 
x_11 = lean::box(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = 0;
lean::inc(x_0);
x_15 = l_lean_run__frontend(x_0, x_1, x_12, x_13, x_3, x_4);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_23 = x_16;
} else {
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
x_8 = x_24;
x_9 = x_18;
goto lbl_10;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_25 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_27 = x_16;
} else {
 lean::inc(x_25);
 lean::dec(x_16);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_15, 1);
lean::inc(x_28);
lean::dec(x_15);
x_31 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_33 = x_25;
} else {
 lean::inc(x_31);
 lean::dec(x_25);
 x_33 = lean::box(0);
}
x_34 = lean::box(0);
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_31);
if (lean::is_scalar(x_27)) {
 x_36 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_36 = x_27;
}
lean::cnstr_set(x_36, 0, x_35);
x_8 = x_36;
x_9 = x_28;
goto lbl_10;
}
}
else
{
obj* x_38; obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_15, 0);
x_40 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_42 = x_15;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_15);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_38);
lean::cnstr_set(x_43, 1, x_40);
return x_43;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_5);
x_45 = l_lean_process__file___closed__1;
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_6);
return x_46;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_49 = x_5;
} else {
 lean::inc(x_47);
 lean::dec(x_5);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_6);
return x_51;
}
}
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_52; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_8, 0);
lean::inc(x_52);
lean::dec(x_8);
x_55 = lean::box(0);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_9);
if (x_2 == 0)
{
obj* x_57; obj* x_58; uint8 x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_57 = lean::box(0);
x_58 = l_lean_elaborator_notation_elaborate___closed__1;
x_59 = 2;
x_60 = l_string_iterator_extract___main___closed__1;
lean::inc(x_52);
x_62 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_62, 0, x_0);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set(x_62, 2, x_57);
lean::cnstr_set(x_62, 3, x_60);
lean::cnstr_set(x_62, 4, x_52);
lean::cnstr_set_scalar(x_62, sizeof(void*)*5, x_59);
x_63 = x_62;
x_64 = l_lean_message_to__string(x_63);
x_65 = l_io_println___at_lean_process__file___spec__1(x_64, x_56);
lean::dec(x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_67; 
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_70; obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_52);
x_70 = lean::cnstr_get(x_65, 1);
lean::inc(x_70);
lean::dec(x_65);
x_73 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_75 = x_67;
} else {
 lean::inc(x_73);
 lean::dec(x_67);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
x_5 = x_76;
x_6 = x_70;
goto lbl_7;
}
else
{
obj* x_77; obj* x_78; obj* x_81; 
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_77 = x_67;
} else {
 lean::dec(x_67);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_65, 1);
lean::inc(x_78);
lean::dec(x_65);
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_77;
 lean::cnstr_set_tag(x_77, 0);
}
lean::cnstr_set(x_81, 0, x_52);
x_5 = x_81;
x_6 = x_78;
goto lbl_7;
}
}
else
{
obj* x_83; obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_52);
x_83 = lean::cnstr_get(x_65, 0);
x_85 = lean::cnstr_get(x_65, 1);
if (lean::is_exclusive(x_65)) {
 x_87 = x_65;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_65);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_83);
lean::cnstr_set(x_88, 1, x_85);
return x_88;
}
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_0);
lean::inc(x_52);
x_91 = l_string_quote(x_52);
x_92 = l_lean_process__file___closed__2;
x_93 = lean::string_append(x_92, x_91);
lean::dec(x_91);
x_95 = l_lean_process__file___lambda__1___closed__7;
x_96 = lean::string_append(x_93, x_95);
x_97 = l_io_println___at_lean_process__file___spec__1(x_96, x_56);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; 
x_99 = lean::cnstr_get(x_97, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_102; obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_52);
x_102 = lean::cnstr_get(x_97, 1);
lean::inc(x_102);
lean::dec(x_97);
x_105 = lean::cnstr_get(x_99, 0);
if (lean::is_exclusive(x_99)) {
 x_107 = x_99;
} else {
 lean::inc(x_105);
 lean::dec(x_99);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
x_5 = x_108;
x_6 = x_102;
goto lbl_7;
}
else
{
obj* x_109; obj* x_110; obj* x_113; 
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 x_109 = x_99;
} else {
 lean::dec(x_99);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_97, 1);
lean::inc(x_110);
lean::dec(x_97);
if (lean::is_scalar(x_109)) {
 x_113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_113 = x_109;
 lean::cnstr_set_tag(x_109, 0);
}
lean::cnstr_set(x_113, 0, x_52);
x_5 = x_113;
x_6 = x_110;
goto lbl_7;
}
}
else
{
obj* x_115; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_52);
x_115 = lean::cnstr_get(x_97, 0);
x_117 = lean::cnstr_get(x_97, 1);
if (lean::is_exclusive(x_97)) {
 x_119 = x_97;
} else {
 lean::inc(x_115);
 lean::inc(x_117);
 lean::dec(x_97);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_115);
lean::cnstr_set(x_120, 1, x_117);
return x_120;
}
}
}
else
{
lean::dec(x_0);
x_5 = x_8;
x_6 = x_9;
goto lbl_7;
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
 l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__1 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__1();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__1);
 l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__2 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__2();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__2);
 l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__3 = _init_l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__3();
lean::mark_persistent(l_io_prim_iterate___at_lean_run__frontend___spec__5___lambda__4___closed__3);
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

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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__3;
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_process__file___lambda__1___closed__6;
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__6;
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_parser_parse__command(obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_string_quote(obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__1;
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_process__file___closed__1;
obj* l_io_println___at_lean_run__frontend___spec__3___boxed(obj*, obj*);
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11(obj*, uint8, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj*, obj*, obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_lean_elaborator_run(obj*);
extern obj* l_lean_format_be___main___closed__1;
extern obj* l_string_join___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__4;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__10(obj*, obj*, obj*, uint8, obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__1(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_lean_parser_parse__header(obj*);
obj* l_reader__t_monad___rarg___lambda__9___boxed(obj*, obj*, obj*);
obj* l_io_print___at_lean_run__frontend___spec__4(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_println___at_lean_run__frontend___spec__3(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_io_print___at_lean_run__frontend___spec__4___boxed(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__2;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5___boxed(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_lean_profileit__pure___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__4;
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
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1) {
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
obj* l_io_print___at_lean_run__frontend___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_lean_run__frontend___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
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
x_18 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_17, x_14);
return x_18;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__command(x_0, x_1);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_expand(x_0, x_1);
return x_3;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborator died!!");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_list_reverse___rarg(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parser died!!");
return x_0;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_30; obj* x_33; obj* x_36; obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; 
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_7, 0);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
lean::dec(x_9);
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_11, 1);
lean::inc(x_24);
lean::dec(x_11);
x_27 = lean::box(0);
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
lean::dec(x_28);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
lean::dec(x_30);
x_36 = lean::cnstr_get(x_33, 2);
lean::inc(x_36);
lean::dec(x_33);
x_39 = lean::cnstr_get(x_13, 0);
lean::inc(x_39);
x_41 = lean::string_iterator_offset(x_39);
lean::dec(x_39);
x_43 = l_lean_file__map_to__position(x_36, x_41);
lean::inc(x_19);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__1___boxed), 3, 2);
lean::closure_set(x_45, 0, x_19);
lean::closure_set(x_45, 1, x_13);
x_46 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__1;
x_47 = l_lean_profileit__pure___rarg(x_46, x_43, x_45, x_3);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_52; obj* x_54; obj* x_55; obj* x_58; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_69; 
x_52 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_set(x_50, 0, lean::box(0));
 x_54 = x_50;
} else {
 lean::inc(x_52);
 lean::dec(x_50);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_47, 1);
lean::inc(x_55);
lean::dec(x_47);
x_58 = lean::cnstr_get(x_48, 1);
lean::inc(x_58);
lean::dec(x_48);
x_61 = lean::cnstr_get(x_52, 0);
x_63 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_set(x_52, 0, lean::box(0));
 lean::cnstr_set(x_52, 1, lean::box(0));
 x_65 = x_52;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_52);
 x_65 = lean::box(0);
}
x_66 = l_list_reverse___rarg(x_58);
lean::inc(x_0);
x_68 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_0, x_66, x_55);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_80; obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_16);
lean::dec(x_22);
lean::dec(x_43);
lean::dec(x_19);
lean::dec(x_24);
lean::dec(x_54);
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_65);
x_80 = lean::cnstr_get(x_68, 1);
lean::inc(x_80);
lean::dec(x_68);
x_83 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 x_85 = x_69;
} else {
 lean::inc(x_83);
 lean::dec(x_69);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
x_4 = x_86;
x_5 = x_80;
goto lbl_6;
}
else
{
obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_69);
x_88 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_set(x_68, 1, lean::box(0));
 x_90 = x_68;
} else {
 lean::inc(x_88);
 lean::dec(x_68);
 x_90 = lean::box(0);
}
lean::inc(x_22);
lean::inc(x_61);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__2___boxed), 3, 2);
lean::closure_set(x_93, 0, x_61);
lean::closure_set(x_93, 1, x_22);
x_94 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__2;
x_95 = l_lean_profileit__pure___rarg(x_94, x_43, x_93, x_88);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
if (lean::obj_tag(x_96) == 0)
{
lean::dec(x_43);
if (x_1 == 0)
{
obj* x_101; obj* x_103; obj* x_104; obj* x_108; obj* x_109; 
lean::dec(x_24);
lean::dec(x_61);
x_101 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_set(x_95, 1, lean::box(0));
 x_103 = x_95;
} else {
 lean::inc(x_101);
 lean::dec(x_95);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_96, 0);
lean::inc(x_104);
lean::dec(x_96);
lean::inc(x_0);
x_108 = lean::apply_2(x_0, x_104, x_101);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
if (lean::obj_tag(x_109) == 0)
{
obj* x_119; obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_16);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_103);
lean::dec(x_54);
lean::dec(x_90);
lean::dec(x_63);
lean::dec(x_65);
x_119 = lean::cnstr_get(x_108, 1);
lean::inc(x_119);
lean::dec(x_108);
x_122 = lean::cnstr_get(x_109, 0);
if (lean::is_exclusive(x_109)) {
 x_124 = x_109;
} else {
 lean::inc(x_122);
 lean::dec(x_109);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
x_4 = x_125;
x_5 = x_119;
goto lbl_6;
}
else
{
obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_126 = x_109;
} else {
 lean::dec(x_109);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_129 = x_108;
} else {
 lean::inc(x_127);
 lean::dec(x_108);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_22);
lean::cnstr_set(x_130, 1, x_27);
if (lean::is_scalar(x_103)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_103;
}
lean::cnstr_set(x_131, 0, x_19);
lean::cnstr_set(x_131, 1, x_130);
if (lean::is_scalar(x_90)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_90;
}
lean::cnstr_set(x_132, 0, x_16);
lean::cnstr_set(x_132, 1, x_131);
if (lean::is_scalar(x_65)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_65;
}
lean::cnstr_set(x_133, 0, x_63);
lean::cnstr_set(x_133, 1, x_132);
if (lean::is_scalar(x_54)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_54;
}
lean::cnstr_set(x_134, 0, x_133);
if (lean::is_scalar(x_126)) {
 x_135 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_135 = x_126;
}
lean::cnstr_set(x_135, 0, x_134);
x_4 = x_135;
x_5 = x_127;
goto lbl_6;
}
}
else
{
obj* x_136; obj* x_138; obj* x_139; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_set(x_95, 1, lean::box(0));
 x_138 = x_95;
} else {
 lean::inc(x_136);
 lean::dec(x_95);
 x_138 = lean::box(0);
}
x_139 = lean::cnstr_get(x_96, 0);
lean::inc(x_139);
lean::dec(x_96);
lean::inc(x_0);
x_143 = lean::apply_2(x_0, x_139, x_136);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
if (lean::obj_tag(x_144) == 0)
{
obj* x_156; obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_16);
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_24);
lean::dec(x_54);
lean::dec(x_90);
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_65);
lean::dec(x_138);
x_156 = lean::cnstr_get(x_143, 1);
lean::inc(x_156);
lean::dec(x_143);
x_159 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_161 = x_144;
} else {
 lean::inc(x_159);
 lean::dec(x_144);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_159);
x_4 = x_162;
x_5 = x_156;
goto lbl_6;
}
else
{
obj* x_163; obj* x_164; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 x_163 = x_144;
} else {
 lean::dec(x_144);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_143, 1);
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 x_166 = x_143;
} else {
 lean::inc(x_164);
 lean::dec(x_143);
 x_166 = lean::box(0);
}
x_167 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_167, 0, x_61);
lean::cnstr_set(x_167, 1, x_24);
if (lean::is_scalar(x_166)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_166;
}
lean::cnstr_set(x_168, 0, x_22);
lean::cnstr_set(x_168, 1, x_167);
if (lean::is_scalar(x_138)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_138;
}
lean::cnstr_set(x_169, 0, x_19);
lean::cnstr_set(x_169, 1, x_168);
if (lean::is_scalar(x_90)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_90;
}
lean::cnstr_set(x_170, 0, x_16);
lean::cnstr_set(x_170, 1, x_169);
if (lean::is_scalar(x_65)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_65;
}
lean::cnstr_set(x_171, 0, x_63);
lean::cnstr_set(x_171, 1, x_170);
if (lean::is_scalar(x_54)) {
 x_172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_172 = x_54;
}
lean::cnstr_set(x_172, 0, x_171);
if (lean::is_scalar(x_163)) {
 x_173 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_173 = x_163;
}
lean::cnstr_set(x_173, 0, x_172);
x_4 = x_173;
x_5 = x_164;
goto lbl_6;
}
}
}
else
{
obj* x_177; obj* x_179; obj* x_180; obj* x_184; obj* x_185; obj* x_186; obj* x_188; 
lean::dec(x_22);
lean::dec(x_19);
lean::dec(x_65);
x_177 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_set(x_95, 1, lean::box(0));
 x_179 = x_95;
} else {
 lean::inc(x_177);
 lean::dec(x_95);
 x_179 = lean::box(0);
}
x_180 = lean::cnstr_get(x_96, 0);
lean::inc(x_180);
lean::dec(x_96);
lean::inc(x_180);
x_184 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_184, 0, x_16);
lean::closure_set(x_184, 1, x_180);
x_185 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__3;
x_186 = l_lean_profileit__pure___rarg(x_185, x_43, x_184, x_177);
lean::dec(x_43);
x_188 = lean::cnstr_get(x_186, 0);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
obj* x_193; obj* x_196; obj* x_199; uint8 x_200; 
lean::dec(x_90);
lean::dec(x_63);
lean::dec(x_179);
x_193 = lean::cnstr_get(x_186, 1);
lean::inc(x_193);
lean::dec(x_186);
x_196 = lean::cnstr_get(x_188, 0);
lean::inc(x_196);
lean::dec(x_188);
x_199 = l_lean_parser_module_eoi;
x_200 = l_lean_parser_syntax_is__of__kind___main(x_199, x_180);
lean::dec(x_180);
if (x_200 == 0)
{
obj* x_202; obj* x_203; obj* x_204; 
x_202 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__4;
x_203 = l_io_println___at_lean_run__frontend___spec__3(x_202, x_193);
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
if (lean::obj_tag(x_204) == 0)
{
obj* x_210; obj* x_213; obj* x_215; obj* x_216; 
lean::dec(x_196);
lean::dec(x_24);
lean::dec(x_54);
lean::dec(x_61);
x_210 = lean::cnstr_get(x_203, 1);
lean::inc(x_210);
lean::dec(x_203);
x_213 = lean::cnstr_get(x_204, 0);
if (lean::is_exclusive(x_204)) {
 x_215 = x_204;
} else {
 lean::inc(x_213);
 lean::dec(x_204);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
x_4 = x_216;
x_5 = x_210;
goto lbl_6;
}
else
{
obj* x_218; obj* x_221; obj* x_223; obj* x_224; 
lean::dec(x_204);
x_218 = lean::cnstr_get(x_203, 1);
lean::inc(x_218);
lean::dec(x_203);
x_221 = l_list_reverse___rarg(x_196);
lean::inc(x_0);
x_223 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(x_0, x_221, x_218);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
if (lean::obj_tag(x_224) == 0)
{
obj* x_229; obj* x_232; obj* x_234; obj* x_235; 
lean::dec(x_24);
lean::dec(x_54);
lean::dec(x_61);
x_229 = lean::cnstr_get(x_223, 1);
lean::inc(x_229);
lean::dec(x_223);
x_232 = lean::cnstr_get(x_224, 0);
if (lean::is_exclusive(x_224)) {
 x_234 = x_224;
} else {
 lean::inc(x_232);
 lean::dec(x_224);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_232);
x_4 = x_235;
x_5 = x_229;
goto lbl_6;
}
else
{
obj* x_236; 
if (lean::is_exclusive(x_224)) {
 lean::cnstr_release(x_224, 0);
 x_236 = x_224;
} else {
 lean::dec(x_224);
 x_236 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_241; obj* x_244; 
lean::dec(x_236);
lean::dec(x_24);
lean::dec(x_54);
lean::dec(x_61);
x_241 = lean::cnstr_get(x_223, 1);
lean::inc(x_241);
lean::dec(x_223);
x_244 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5;
x_4 = x_244;
x_5 = x_241;
goto lbl_6;
}
else
{
obj* x_245; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
x_245 = lean::cnstr_get(x_223, 1);
lean::inc(x_245);
lean::dec(x_223);
x_248 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_248, 0, x_61);
lean::cnstr_set(x_248, 1, x_24);
x_249 = l_list_reverse___rarg(x_248);
if (lean::is_scalar(x_54)) {
 x_250 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_250 = x_54;
 lean::cnstr_set_tag(x_54, 1);
}
lean::cnstr_set(x_250, 0, x_249);
if (lean::is_scalar(x_236)) {
 x_251 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_251 = x_236;
}
lean::cnstr_set(x_251, 0, x_250);
x_4 = x_251;
x_5 = x_245;
goto lbl_6;
}
}
}
}
else
{
obj* x_252; obj* x_254; obj* x_255; 
x_252 = l_list_reverse___rarg(x_196);
lean::inc(x_0);
x_254 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_252, x_193);
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
if (lean::obj_tag(x_255) == 0)
{
obj* x_260; obj* x_263; obj* x_265; obj* x_266; 
lean::dec(x_24);
lean::dec(x_54);
lean::dec(x_61);
x_260 = lean::cnstr_get(x_254, 1);
lean::inc(x_260);
lean::dec(x_254);
x_263 = lean::cnstr_get(x_255, 0);
if (lean::is_exclusive(x_255)) {
 x_265 = x_255;
} else {
 lean::inc(x_263);
 lean::dec(x_255);
 x_265 = lean::box(0);
}
if (lean::is_scalar(x_265)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_265;
}
lean::cnstr_set(x_266, 0, x_263);
x_4 = x_266;
x_5 = x_260;
goto lbl_6;
}
else
{
obj* x_267; 
if (lean::is_exclusive(x_255)) {
 lean::cnstr_release(x_255, 0);
 x_267 = x_255;
} else {
 lean::dec(x_255);
 x_267 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_272; obj* x_275; 
lean::dec(x_24);
lean::dec(x_267);
lean::dec(x_54);
lean::dec(x_61);
x_272 = lean::cnstr_get(x_254, 1);
lean::inc(x_272);
lean::dec(x_254);
x_275 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5;
x_4 = x_275;
x_5 = x_272;
goto lbl_6;
}
else
{
obj* x_276; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_276 = lean::cnstr_get(x_254, 1);
lean::inc(x_276);
lean::dec(x_254);
x_279 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_279, 0, x_61);
lean::cnstr_set(x_279, 1, x_24);
x_280 = l_list_reverse___rarg(x_279);
if (lean::is_scalar(x_54)) {
 x_281 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_281 = x_54;
 lean::cnstr_set_tag(x_54, 1);
}
lean::cnstr_set(x_281, 0, x_280);
if (lean::is_scalar(x_267)) {
 x_282 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_282 = x_267;
}
lean::cnstr_set(x_282, 0, x_281);
x_4 = x_282;
x_5 = x_276;
goto lbl_6;
}
}
}
}
else
{
obj* x_284; obj* x_286; obj* x_287; obj* x_289; obj* x_292; obj* x_294; obj* x_296; obj* x_297; 
lean::dec(x_180);
x_284 = lean::cnstr_get(x_186, 1);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 lean::cnstr_set(x_186, 1, lean::box(0));
 x_286 = x_186;
} else {
 lean::inc(x_284);
 lean::dec(x_186);
 x_286 = lean::box(0);
}
x_287 = lean::cnstr_get(x_188, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_188, 1);
lean::inc(x_289);
lean::dec(x_188);
x_292 = lean::cnstr_get(x_287, 5);
lean::inc(x_292);
x_294 = l_list_reverse___rarg(x_292);
lean::inc(x_0);
x_296 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_294, x_284);
x_297 = lean::cnstr_get(x_296, 0);
lean::inc(x_297);
if (lean::obj_tag(x_297) == 0)
{
obj* x_308; obj* x_311; obj* x_313; obj* x_314; 
lean::dec(x_287);
lean::dec(x_24);
lean::dec(x_286);
lean::dec(x_289);
lean::dec(x_54);
lean::dec(x_90);
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_179);
x_308 = lean::cnstr_get(x_296, 1);
lean::inc(x_308);
lean::dec(x_296);
x_311 = lean::cnstr_get(x_297, 0);
if (lean::is_exclusive(x_297)) {
 x_313 = x_297;
} else {
 lean::inc(x_311);
 lean::dec(x_297);
 x_313 = lean::box(0);
}
if (lean::is_scalar(x_313)) {
 x_314 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_314 = x_313;
}
lean::cnstr_set(x_314, 0, x_311);
x_4 = x_314;
x_5 = x_308;
goto lbl_6;
}
else
{
obj* x_315; 
if (lean::is_exclusive(x_297)) {
 lean::cnstr_release(x_297, 0);
 x_315 = x_297;
} else {
 lean::dec(x_297);
 x_315 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_318; obj* x_320; obj* x_321; obj* x_323; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; 
lean::dec(x_24);
lean::dec(x_61);
x_318 = lean::cnstr_get(x_296, 1);
if (lean::is_exclusive(x_296)) {
 lean::cnstr_release(x_296, 0);
 x_320 = x_296;
} else {
 lean::inc(x_318);
 lean::dec(x_296);
 x_320 = lean::box(0);
}
x_321 = lean::cnstr_get(x_287, 6);
lean::inc(x_321);
x_323 = lean::cnstr_get(x_287, 7);
lean::inc(x_323);
lean::dec(x_287);
if (lean::is_scalar(x_320)) {
 x_326 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_326 = x_320;
}
lean::cnstr_set(x_326, 0, x_323);
lean::cnstr_set(x_326, 1, x_27);
if (lean::is_scalar(x_286)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_286;
}
lean::cnstr_set(x_327, 0, x_321);
lean::cnstr_set(x_327, 1, x_326);
if (lean::is_scalar(x_179)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_179;
}
lean::cnstr_set(x_328, 0, x_289);
lean::cnstr_set(x_328, 1, x_327);
if (lean::is_scalar(x_90)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_90;
}
lean::cnstr_set(x_329, 0, x_63);
lean::cnstr_set(x_329, 1, x_328);
if (lean::is_scalar(x_54)) {
 x_330 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_330 = x_54;
}
lean::cnstr_set(x_330, 0, x_329);
if (lean::is_scalar(x_315)) {
 x_331 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_331 = x_315;
}
lean::cnstr_set(x_331, 0, x_330);
x_4 = x_331;
x_5 = x_318;
goto lbl_6;
}
else
{
obj* x_332; obj* x_334; obj* x_335; obj* x_337; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; 
x_332 = lean::cnstr_get(x_296, 1);
if (lean::is_exclusive(x_296)) {
 lean::cnstr_release(x_296, 0);
 x_334 = x_296;
} else {
 lean::inc(x_332);
 lean::dec(x_296);
 x_334 = lean::box(0);
}
x_335 = lean::cnstr_get(x_287, 6);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_287, 7);
lean::inc(x_337);
lean::dec(x_287);
x_340 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_340, 0, x_61);
lean::cnstr_set(x_340, 1, x_24);
if (lean::is_scalar(x_334)) {
 x_341 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_341 = x_334;
}
lean::cnstr_set(x_341, 0, x_337);
lean::cnstr_set(x_341, 1, x_340);
if (lean::is_scalar(x_286)) {
 x_342 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_342 = x_286;
}
lean::cnstr_set(x_342, 0, x_335);
lean::cnstr_set(x_342, 1, x_341);
if (lean::is_scalar(x_179)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_179;
}
lean::cnstr_set(x_343, 0, x_289);
lean::cnstr_set(x_343, 1, x_342);
if (lean::is_scalar(x_90)) {
 x_344 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_344 = x_90;
}
lean::cnstr_set(x_344, 0, x_63);
lean::cnstr_set(x_344, 1, x_343);
if (lean::is_scalar(x_54)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_54;
}
lean::cnstr_set(x_345, 0, x_344);
if (lean::is_scalar(x_315)) {
 x_346 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_346 = x_315;
}
lean::cnstr_set(x_346, 0, x_345);
x_4 = x_346;
x_5 = x_332;
goto lbl_6;
}
}
}
}
}
}
else
{
obj* x_351; obj* x_352; obj* x_355; obj* x_358; obj* x_359; obj* x_360; 
lean::dec(x_16);
lean::dec(x_22);
lean::dec(x_43);
lean::dec(x_19);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_351 = x_50;
} else {
 lean::dec(x_50);
 x_351 = lean::box(0);
}
x_352 = lean::cnstr_get(x_47, 1);
lean::inc(x_352);
lean::dec(x_47);
x_355 = lean::cnstr_get(x_48, 1);
lean::inc(x_355);
lean::dec(x_48);
x_358 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__6;
x_359 = l_io_println___at_lean_run__frontend___spec__3(x_358, x_352);
x_360 = lean::cnstr_get(x_359, 0);
lean::inc(x_360);
if (lean::obj_tag(x_360) == 0)
{
obj* x_365; obj* x_368; obj* x_370; obj* x_371; 
lean::dec(x_24);
lean::dec(x_355);
lean::dec(x_351);
x_365 = lean::cnstr_get(x_359, 1);
lean::inc(x_365);
lean::dec(x_359);
x_368 = lean::cnstr_get(x_360, 0);
if (lean::is_exclusive(x_360)) {
 x_370 = x_360;
} else {
 lean::inc(x_368);
 lean::dec(x_360);
 x_370 = lean::box(0);
}
if (lean::is_scalar(x_370)) {
 x_371 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_371 = x_370;
}
lean::cnstr_set(x_371, 0, x_368);
x_4 = x_371;
x_5 = x_365;
goto lbl_6;
}
else
{
obj* x_373; obj* x_376; obj* x_378; obj* x_379; 
lean::dec(x_360);
x_373 = lean::cnstr_get(x_359, 1);
lean::inc(x_373);
lean::dec(x_359);
x_376 = l_list_reverse___rarg(x_355);
lean::inc(x_0);
x_378 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_376, x_373);
x_379 = lean::cnstr_get(x_378, 0);
lean::inc(x_379);
if (lean::obj_tag(x_379) == 0)
{
obj* x_383; obj* x_386; obj* x_388; obj* x_389; 
lean::dec(x_24);
lean::dec(x_351);
x_383 = lean::cnstr_get(x_378, 1);
lean::inc(x_383);
lean::dec(x_378);
x_386 = lean::cnstr_get(x_379, 0);
if (lean::is_exclusive(x_379)) {
 x_388 = x_379;
} else {
 lean::inc(x_386);
 lean::dec(x_379);
 x_388 = lean::box(0);
}
if (lean::is_scalar(x_388)) {
 x_389 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_389 = x_388;
}
lean::cnstr_set(x_389, 0, x_386);
x_4 = x_389;
x_5 = x_383;
goto lbl_6;
}
else
{
obj* x_390; obj* x_391; obj* x_394; obj* x_395; obj* x_396; 
if (lean::is_exclusive(x_379)) {
 lean::cnstr_release(x_379, 0);
 x_390 = x_379;
} else {
 lean::dec(x_379);
 x_390 = lean::box(0);
}
x_391 = lean::cnstr_get(x_378, 1);
lean::inc(x_391);
lean::dec(x_378);
x_394 = l_list_reverse___rarg(x_24);
if (lean::is_scalar(x_351)) {
 x_395 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_395 = x_351;
}
lean::cnstr_set(x_395, 0, x_394);
if (lean::is_scalar(x_390)) {
 x_396 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_396 = x_390;
}
lean::cnstr_set(x_396, 0, x_395);
x_4 = x_396;
x_5 = x_391;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_398; obj* x_400; obj* x_401; obj* x_402; 
lean::dec(x_0);
x_398 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_400 = x_4;
} else {
 lean::inc(x_398);
 lean::dec(x_4);
 x_400 = lean::box(0);
}
if (lean::is_scalar(x_400)) {
 x_401 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_401 = x_400;
}
lean::cnstr_set(x_401, 0, x_398);
x_402 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_402, 0, x_401);
lean::cnstr_set(x_402, 1, x_5);
return x_402;
}
else
{
obj* x_403; obj* x_405; 
x_403 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_405 = x_4;
} else {
 lean::inc(x_403);
 lean::dec(x_4);
 x_405 = lean::box(0);
}
if (lean::obj_tag(x_403) == 0)
{
obj* x_407; 
lean::dec(x_405);
x_407 = lean::cnstr_get(x_403, 0);
lean::inc(x_407);
lean::dec(x_403);
x_2 = x_407;
x_3 = x_5;
goto _start;
}
else
{
obj* x_412; obj* x_415; obj* x_416; 
lean::dec(x_0);
x_412 = lean::cnstr_get(x_403, 0);
lean::inc(x_412);
lean::dec(x_403);
if (lean::is_scalar(x_405)) {
 x_415 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_415 = x_405;
}
lean::cnstr_set(x_415, 0, x_412);
x_416 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_416, 0, x_415);
lean::cnstr_set(x_416, 1, x_5);
return x_416;
}
}
}
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__10(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::inc(x_1);
x_8 = l_lean_file__map_from__string(x_1);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_8);
x_10 = l_lean_expander_builtin__transformers;
lean::inc(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
lean::inc(x_4);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_4);
x_15 = l_lean_elaborator_run(x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11(x_2, x_3, x_20, x_6);
return x_21;
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(obj* x_0, obj* x_1, obj* x_2) {
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
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_36; obj* x_39; obj* x_42; obj* x_45; obj* x_47; obj* x_48; 
x_36 = lean::cnstr_get(x_34, 0);
lean::inc(x_36);
lean::dec(x_34);
x_39 = lean::cnstr_get(x_33, 1);
lean::inc(x_39);
lean::dec(x_33);
x_42 = lean::cnstr_get(x_36, 1);
lean::inc(x_42);
lean::dec(x_36);
x_45 = l_list_reverse___rarg(x_39);
lean::inc(x_2);
x_47 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_45, x_6);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_29);
lean::dec(x_42);
x_55 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_57 = x_47;
} else {
 lean::inc(x_55);
 lean::dec(x_47);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 x_60 = x_48;
} else {
 lean::inc(x_58);
 lean::dec(x_48);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
if (lean::is_scalar(x_57)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_57;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_55);
return x_62;
}
else
{
obj* x_64; obj* x_67; 
lean::dec(x_48);
x_64 = lean::cnstr_get(x_47, 1);
lean::inc(x_64);
lean::dec(x_47);
x_67 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__10(x_0, x_1, x_2, x_3, x_29, x_42, x_64);
return x_67;
}
}
else
{
obj* x_72; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_34);
lean::dec(x_29);
x_72 = lean::cnstr_get(x_33, 1);
lean::inc(x_72);
lean::dec(x_33);
x_75 = l_list_reverse___rarg(x_72);
x_76 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_2, x_75, x_6);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
if (lean::obj_tag(x_77) == 0)
{
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
x_79 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_release(x_76, 0);
 x_81 = x_76;
} else {
 lean::inc(x_79);
 lean::dec(x_76);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_84 = x_77;
} else {
 lean::inc(x_82);
 lean::dec(x_77);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
if (lean::is_scalar(x_81)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_81;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_79);
return x_86;
}
else
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_77);
x_88 = lean::cnstr_get(x_76, 1);
if (lean::is_exclusive(x_76)) {
 lean::cnstr_release(x_76, 0);
 x_90 = x_76;
} else {
 lean::inc(x_88);
 lean::dec(x_76);
 x_90 = lean::box(0);
}
x_91 = l_lean_expander_expand__bracketed__binder___main___closed__4;
if (lean::is_scalar(x_90)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_90;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_88);
return x_92;
}
}
}
}
}
}
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_print___at_lean_run__frontend___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_print___at_lean_run__frontend___spec__4(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_println___at_lean_run__frontend___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_println___at_lean_run__frontend___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_io_prim_iterate___main___at_lean_run__frontend___spec__11(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_3);
x_8 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__10(x_0, x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
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
x_6 = l_io_println___at_lean_run__frontend___spec__3(x_5, x_2);
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
x_48 = l_io_println___at_lean_run__frontend___spec__3(x_47, x_2);
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
x_62 = l_io_println___at_lean_run__frontend___spec__3(x_61, x_2);
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
x_76 = l_io_println___at_lean_run__frontend___spec__3(x_75, x_2);
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
x_23 = l_string_join___closed__1;
x_24 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_24, 0, x_0);
lean::cnstr_set(x_24, 1, x_21);
lean::cnstr_set(x_24, 2, x_20);
lean::cnstr_set(x_24, 3, x_23);
lean::cnstr_set(x_24, 4, x_15);
lean::cnstr_set_scalar(x_24, sizeof(void*)*5, x_22);
x_25 = x_24;
x_26 = l_lean_message_to__string(x_25);
x_27 = l_io_println___at_lean_run__frontend___spec__3(x_26, x_12);
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
x_43 = l_io_println___at_lean_run__frontend___spec__3(x_42, x_12);
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
 l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__1();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__2();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__2);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__3 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__3();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__3);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__4 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__4();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__4);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__5);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__6 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__6();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__11___closed__6);
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

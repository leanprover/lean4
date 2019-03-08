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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6(obj*, obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
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
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
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
extern obj* l_string_join___closed__1;
obj* l_io_println___at_lean_process__file___spec__1(obj*, obj*);
extern obj* l_lean_options_mk;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1;
obj* l_lean_parser_parse__header(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj*, obj*, obj*, uint8, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1___closed__1;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__4;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___closed__1;
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
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_20; obj* x_23; obj* x_26; obj* x_28; obj* x_32; obj* x_34; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_46; obj* x_49; obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
lean::dec(x_13);
x_26 = lean::cnstr_get(x_15, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_15, 1);
lean::inc(x_28);
lean::dec(x_15);
lean::inc(x_5);
x_32 = l_list_reverse___rarg(x_5);
lean::inc(x_1);
x_34 = l_lean_file__map_from__string(x_1);
lean::inc(x_1);
lean::inc(x_0);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_0);
lean::cnstr_set(x_37, 1, x_1);
lean::cnstr_set(x_37, 2, x_34);
lean::inc(x_4);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_4);
x_40 = lean::box(0);
x_41 = lean::cnstr_get(x_23, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
lean::dec(x_41);
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
lean::dec(x_43);
x_49 = lean::cnstr_get(x_46, 2);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::cnstr_get(x_17, 0);
lean::inc(x_52);
x_54 = lean::string_iterator_offset(x_52);
lean::dec(x_52);
x_56 = l_lean_file__map_to__position(x_49, x_54);
lean::inc(x_23);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_58, 0, x_23);
lean::closure_set(x_58, 1, x_17);
x_59 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__1;
x_60 = l_lean_profileit__pure___rarg(x_59, x_56, x_58, x_7);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_61, 1);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_70; obj* x_73; obj* x_76; obj* x_80; obj* x_81; 
lean::dec(x_23);
lean::dec(x_26);
lean::dec(x_39);
lean::dec(x_20);
lean::dec(x_56);
x_70 = lean::cnstr_get(x_60, 1);
lean::inc(x_70);
lean::dec(x_60);
x_73 = lean::cnstr_get(x_61, 0);
lean::inc(x_73);
lean::dec(x_61);
x_76 = lean::cnstr_get(x_63, 0);
lean::inc(x_76);
lean::dec(x_63);
lean::inc(x_2);
x_80 = lean::apply_2(x_2, x_76, x_70);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
if (lean::obj_tag(x_81) == 0)
{
obj* x_86; obj* x_89; obj* x_91; obj* x_92; 
lean::dec(x_28);
lean::dec(x_32);
lean::dec(x_73);
x_86 = lean::cnstr_get(x_80, 1);
lean::inc(x_86);
lean::dec(x_80);
x_89 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_91 = x_81;
} else {
 lean::inc(x_89);
 lean::dec(x_81);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
x_8 = x_92;
x_9 = x_86;
goto lbl_10;
}
else
{
obj* x_94; obj* x_98; obj* x_99; 
lean::dec(x_81);
x_94 = lean::cnstr_get(x_80, 1);
lean::inc(x_94);
lean::dec(x_80);
lean::inc(x_2);
x_98 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_2, x_32, x_94);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_103; obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_28);
lean::dec(x_73);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
lean::dec(x_98);
x_106 = lean::cnstr_get(x_99, 0);
if (lean::is_exclusive(x_99)) {
 x_108 = x_99;
} else {
 lean::inc(x_106);
 lean::dec(x_99);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
x_8 = x_109;
x_9 = x_103;
goto lbl_10;
}
else
{
obj* x_110; 
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 x_110 = x_99;
} else {
 lean::dec(x_99);
 x_110 = lean::box(0);
}
if (x_3 == 0)
{
obj* x_114; obj* x_117; 
lean::dec(x_110);
lean::dec(x_28);
lean::dec(x_73);
x_114 = lean::cnstr_get(x_98, 1);
lean::inc(x_114);
lean::dec(x_98);
x_117 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2;
x_8 = x_117;
x_9 = x_114;
goto lbl_10;
}
else
{
obj* x_118; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_118 = lean::cnstr_get(x_98, 1);
lean::inc(x_118);
lean::dec(x_98);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_73);
lean::cnstr_set(x_121, 1, x_28);
x_122 = l_list_reverse___rarg(x_121);
x_123 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_123, 0, x_122);
if (lean::is_scalar(x_110)) {
 x_124 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_124 = x_110;
}
lean::cnstr_set(x_124, 0, x_123);
x_8 = x_124;
x_9 = x_118;
goto lbl_10;
}
}
}
}
else
{
obj* x_126; obj* x_129; obj* x_132; obj* x_135; obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_143; 
lean::dec(x_32);
x_126 = lean::cnstr_get(x_63, 0);
lean::inc(x_126);
lean::dec(x_63);
x_129 = lean::cnstr_get(x_60, 1);
lean::inc(x_129);
lean::dec(x_60);
x_132 = lean::cnstr_get(x_61, 0);
lean::inc(x_132);
lean::dec(x_61);
x_135 = lean::cnstr_get(x_126, 0);
x_137 = lean::cnstr_get(x_126, 1);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_set(x_126, 0, lean::box(0));
 lean::cnstr_set(x_126, 1, lean::box(0));
 x_139 = x_126;
} else {
 lean::inc(x_135);
 lean::inc(x_137);
 lean::dec(x_126);
 x_139 = lean::box(0);
}
x_140 = l_list_reverse___rarg(x_137);
lean::inc(x_2);
x_142 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(x_2, x_140, x_129);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_154; obj* x_157; obj* x_159; obj* x_160; 
lean::dec(x_23);
lean::dec(x_26);
lean::dec(x_39);
lean::dec(x_20);
lean::dec(x_28);
lean::dec(x_56);
lean::dec(x_139);
lean::dec(x_132);
lean::dec(x_135);
x_154 = lean::cnstr_get(x_142, 1);
lean::inc(x_154);
lean::dec(x_142);
x_157 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_159 = x_143;
} else {
 lean::inc(x_157);
 lean::dec(x_143);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
x_8 = x_160;
x_9 = x_154;
goto lbl_10;
}
else
{
obj* x_161; obj* x_162; obj* x_164; obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 x_161 = x_143;
} else {
 lean::dec(x_143);
 x_161 = lean::box(0);
}
x_162 = lean::cnstr_get(x_142, 1);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_set(x_142, 1, lean::box(0));
 x_164 = x_142;
} else {
 lean::inc(x_162);
 lean::dec(x_142);
 x_164 = lean::box(0);
}
lean::inc(x_26);
lean::inc(x_132);
x_167 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_167, 0, x_132);
lean::closure_set(x_167, 1, x_26);
x_168 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__3;
x_169 = l_lean_profileit__pure___rarg(x_168, x_56, x_167, x_162);
x_170 = lean::cnstr_get(x_169, 0);
lean::inc(x_170);
if (lean::obj_tag(x_170) == 0)
{
lean::dec(x_39);
lean::dec(x_56);
lean::dec(x_161);
if (x_3 == 0)
{
obj* x_177; obj* x_179; obj* x_180; obj* x_184; obj* x_185; 
lean::dec(x_28);
lean::dec(x_132);
x_177 = lean::cnstr_get(x_169, 1);
if (lean::is_exclusive(x_169)) {
 lean::cnstr_release(x_169, 0);
 lean::cnstr_set(x_169, 1, lean::box(0));
 x_179 = x_169;
} else {
 lean::inc(x_177);
 lean::dec(x_169);
 x_179 = lean::box(0);
}
x_180 = lean::cnstr_get(x_170, 0);
lean::inc(x_180);
lean::dec(x_170);
lean::inc(x_2);
x_184 = lean::apply_2(x_2, x_180, x_177);
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
if (lean::obj_tag(x_185) == 0)
{
obj* x_194; obj* x_197; obj* x_199; obj* x_200; 
lean::dec(x_23);
lean::dec(x_26);
lean::dec(x_20);
lean::dec(x_164);
lean::dec(x_179);
lean::dec(x_139);
lean::dec(x_135);
x_194 = lean::cnstr_get(x_184, 1);
lean::inc(x_194);
lean::dec(x_184);
x_197 = lean::cnstr_get(x_185, 0);
if (lean::is_exclusive(x_185)) {
 x_199 = x_185;
} else {
 lean::inc(x_197);
 lean::dec(x_185);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_197);
x_8 = x_200;
x_9 = x_194;
goto lbl_10;
}
else
{
obj* x_201; obj* x_202; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
if (lean::is_exclusive(x_185)) {
 lean::cnstr_release(x_185, 0);
 x_201 = x_185;
} else {
 lean::dec(x_185);
 x_201 = lean::box(0);
}
x_202 = lean::cnstr_get(x_184, 1);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_204 = x_184;
} else {
 lean::inc(x_202);
 lean::dec(x_184);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_26);
lean::cnstr_set(x_205, 1, x_40);
if (lean::is_scalar(x_179)) {
 x_206 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_206 = x_179;
}
lean::cnstr_set(x_206, 0, x_23);
lean::cnstr_set(x_206, 1, x_205);
if (lean::is_scalar(x_164)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_164;
}
lean::cnstr_set(x_207, 0, x_20);
lean::cnstr_set(x_207, 1, x_206);
if (lean::is_scalar(x_139)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_139;
}
lean::cnstr_set(x_208, 0, x_135);
lean::cnstr_set(x_208, 1, x_207);
x_209 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_209, 0, x_208);
if (lean::is_scalar(x_201)) {
 x_210 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_210 = x_201;
}
lean::cnstr_set(x_210, 0, x_209);
x_8 = x_210;
x_9 = x_202;
goto lbl_10;
}
}
else
{
obj* x_211; obj* x_213; obj* x_214; obj* x_218; obj* x_219; 
x_211 = lean::cnstr_get(x_169, 1);
if (lean::is_exclusive(x_169)) {
 lean::cnstr_release(x_169, 0);
 lean::cnstr_set(x_169, 1, lean::box(0));
 x_213 = x_169;
} else {
 lean::inc(x_211);
 lean::dec(x_169);
 x_213 = lean::box(0);
}
x_214 = lean::cnstr_get(x_170, 0);
lean::inc(x_214);
lean::dec(x_170);
lean::inc(x_2);
x_218 = lean::apply_2(x_2, x_214, x_211);
x_219 = lean::cnstr_get(x_218, 0);
lean::inc(x_219);
if (lean::obj_tag(x_219) == 0)
{
obj* x_230; obj* x_233; obj* x_235; obj* x_236; 
lean::dec(x_213);
lean::dec(x_23);
lean::dec(x_26);
lean::dec(x_20);
lean::dec(x_28);
lean::dec(x_164);
lean::dec(x_139);
lean::dec(x_132);
lean::dec(x_135);
x_230 = lean::cnstr_get(x_218, 1);
lean::inc(x_230);
lean::dec(x_218);
x_233 = lean::cnstr_get(x_219, 0);
if (lean::is_exclusive(x_219)) {
 x_235 = x_219;
} else {
 lean::inc(x_233);
 lean::dec(x_219);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
x_8 = x_236;
x_9 = x_230;
goto lbl_10;
}
else
{
obj* x_237; obj* x_238; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; 
if (lean::is_exclusive(x_219)) {
 lean::cnstr_release(x_219, 0);
 x_237 = x_219;
} else {
 lean::dec(x_219);
 x_237 = lean::box(0);
}
x_238 = lean::cnstr_get(x_218, 1);
if (lean::is_exclusive(x_218)) {
 lean::cnstr_release(x_218, 0);
 x_240 = x_218;
} else {
 lean::inc(x_238);
 lean::dec(x_218);
 x_240 = lean::box(0);
}
x_241 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_241, 0, x_132);
lean::cnstr_set(x_241, 1, x_28);
if (lean::is_scalar(x_240)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_240;
}
lean::cnstr_set(x_242, 0, x_26);
lean::cnstr_set(x_242, 1, x_241);
if (lean::is_scalar(x_213)) {
 x_243 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_243 = x_213;
}
lean::cnstr_set(x_243, 0, x_23);
lean::cnstr_set(x_243, 1, x_242);
if (lean::is_scalar(x_164)) {
 x_244 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_244 = x_164;
}
lean::cnstr_set(x_244, 0, x_20);
lean::cnstr_set(x_244, 1, x_243);
if (lean::is_scalar(x_139)) {
 x_245 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_245 = x_139;
}
lean::cnstr_set(x_245, 0, x_135);
lean::cnstr_set(x_245, 1, x_244);
x_246 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_246, 0, x_245);
if (lean::is_scalar(x_237)) {
 x_247 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_247 = x_237;
}
lean::cnstr_set(x_247, 0, x_246);
x_8 = x_247;
x_9 = x_238;
goto lbl_10;
}
}
}
else
{
obj* x_251; obj* x_253; obj* x_254; obj* x_256; obj* x_258; obj* x_259; obj* x_260; obj* x_262; obj* x_264; obj* x_266; obj* x_267; obj* x_269; obj* x_271; obj* x_272; obj* x_274; obj* x_276; obj* x_277; obj* x_279; 
lean::dec(x_23);
lean::dec(x_26);
lean::dec(x_139);
x_251 = lean::cnstr_get(x_169, 1);
if (lean::is_exclusive(x_169)) {
 lean::cnstr_release(x_169, 0);
 lean::cnstr_set(x_169, 1, lean::box(0));
 x_253 = x_169;
} else {
 lean::inc(x_251);
 lean::dec(x_169);
 x_253 = lean::box(0);
}
x_254 = lean::cnstr_get(x_170, 0);
if (lean::is_exclusive(x_170)) {
 lean::cnstr_set(x_170, 0, lean::box(0));
 x_256 = x_170;
} else {
 lean::inc(x_254);
 lean::dec(x_170);
 x_256 = lean::box(0);
}
lean::inc(x_254);
x_258 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_258, 0, x_39);
lean::closure_set(x_258, 1, x_20);
lean::closure_set(x_258, 2, x_254);
x_259 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__4;
x_260 = l_lean_profileit__pure___rarg(x_259, x_56, x_258, x_251);
lean::dec(x_56);
x_262 = lean::cnstr_get(x_260, 0);
x_264 = lean::cnstr_get(x_260, 1);
if (lean::is_exclusive(x_260)) {
 lean::cnstr_set(x_260, 0, lean::box(0));
 lean::cnstr_set(x_260, 1, lean::box(0));
 x_266 = x_260;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_260);
 x_266 = lean::box(0);
}
x_267 = lean::cnstr_get(x_262, 5);
lean::inc(x_267);
x_269 = l_list_reverse___rarg(x_267);
lean::inc(x_2);
x_271 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_2, x_269, x_264);
x_272 = lean::cnstr_get(x_271, 0);
x_274 = lean::cnstr_get(x_271, 1);
if (lean::is_exclusive(x_271)) {
 lean::cnstr_set(x_271, 0, lean::box(0));
 lean::cnstr_set(x_271, 1, lean::box(0));
 x_276 = x_271;
} else {
 lean::inc(x_272);
 lean::inc(x_274);
 lean::dec(x_271);
 x_276 = lean::box(0);
}
if (lean::obj_tag(x_272) == 0)
{
obj* x_292; obj* x_294; obj* x_295; 
lean::dec(x_262);
lean::dec(x_266);
lean::dec(x_253);
lean::dec(x_254);
lean::dec(x_256);
lean::dec(x_276);
lean::dec(x_28);
lean::dec(x_161);
lean::dec(x_164);
lean::dec(x_132);
lean::dec(x_135);
x_292 = lean::cnstr_get(x_272, 0);
if (lean::is_exclusive(x_272)) {
 x_294 = x_272;
} else {
 lean::inc(x_292);
 lean::dec(x_272);
 x_294 = lean::box(0);
}
if (lean::is_scalar(x_294)) {
 x_295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_295 = x_294;
}
lean::cnstr_set(x_295, 0, x_292);
x_8 = x_295;
x_9 = x_274;
goto lbl_10;
}
else
{
obj* x_297; uint8 x_298; 
lean::dec(x_272);
x_297 = l_lean_parser_module_eoi;
x_298 = l_lean_parser_syntax_is__of__kind___main(x_297, x_254);
lean::dec(x_254);
if (x_298 == 0)
{
obj* x_301; 
lean::dec(x_161);
x_301 = lean::box(0);
x_277 = x_301;
goto lbl_278;
}
else
{
obj* x_309; 
lean::dec(x_262);
lean::dec(x_266);
lean::dec(x_253);
lean::dec(x_256);
lean::dec(x_276);
lean::dec(x_164);
lean::dec(x_135);
x_309 = lean::box(0);
x_279 = x_309;
goto lbl_280;
}
}
lbl_278:
{
lean::dec(x_277);
if (x_3 == 0)
{
obj* x_313; obj* x_315; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
lean::dec(x_28);
lean::dec(x_132);
x_313 = lean::cnstr_get(x_262, 6);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_262, 7);
lean::inc(x_315);
if (lean::is_scalar(x_276)) {
 x_317 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_317 = x_276;
}
lean::cnstr_set(x_317, 0, x_315);
lean::cnstr_set(x_317, 1, x_40);
if (lean::is_scalar(x_266)) {
 x_318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_318 = x_266;
}
lean::cnstr_set(x_318, 0, x_313);
lean::cnstr_set(x_318, 1, x_317);
if (lean::is_scalar(x_253)) {
 x_319 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_319 = x_253;
}
lean::cnstr_set(x_319, 0, x_262);
lean::cnstr_set(x_319, 1, x_318);
if (lean::is_scalar(x_164)) {
 x_320 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_320 = x_164;
}
lean::cnstr_set(x_320, 0, x_135);
lean::cnstr_set(x_320, 1, x_319);
x_321 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_321, 0, x_320);
if (lean::is_scalar(x_256)) {
 x_322 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_322 = x_256;
}
lean::cnstr_set(x_322, 0, x_321);
x_8 = x_322;
x_9 = x_274;
goto lbl_10;
}
else
{
obj* x_323; obj* x_325; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; 
x_323 = lean::cnstr_get(x_262, 6);
lean::inc(x_323);
x_325 = lean::cnstr_get(x_262, 7);
lean::inc(x_325);
x_327 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_327, 0, x_132);
lean::cnstr_set(x_327, 1, x_28);
if (lean::is_scalar(x_276)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_276;
}
lean::cnstr_set(x_328, 0, x_325);
lean::cnstr_set(x_328, 1, x_327);
if (lean::is_scalar(x_266)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_266;
}
lean::cnstr_set(x_329, 0, x_323);
lean::cnstr_set(x_329, 1, x_328);
if (lean::is_scalar(x_253)) {
 x_330 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_330 = x_253;
}
lean::cnstr_set(x_330, 0, x_262);
lean::cnstr_set(x_330, 1, x_329);
if (lean::is_scalar(x_164)) {
 x_331 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_331 = x_164;
}
lean::cnstr_set(x_331, 0, x_135);
lean::cnstr_set(x_331, 1, x_330);
x_332 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_332, 0, x_331);
if (lean::is_scalar(x_256)) {
 x_333 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_333 = x_256;
}
lean::cnstr_set(x_333, 0, x_332);
x_8 = x_333;
x_9 = x_274;
goto lbl_10;
}
}
lbl_280:
{
lean::dec(x_279);
if (x_3 == 0)
{
obj* x_338; 
lean::dec(x_28);
lean::dec(x_161);
lean::dec(x_132);
x_338 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__2;
x_8 = x_338;
x_9 = x_274;
goto lbl_10;
}
else
{
obj* x_339; obj* x_340; obj* x_341; obj* x_342; 
x_339 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_339, 0, x_132);
lean::cnstr_set(x_339, 1, x_28);
x_340 = l_list_reverse___rarg(x_339);
x_341 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_341, 0, x_340);
if (lean::is_scalar(x_161)) {
 x_342 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_342 = x_161;
}
lean::cnstr_set(x_342, 0, x_341);
x_8 = x_342;
x_9 = x_274;
goto lbl_10;
}
}
}
}
}
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_348; obj* x_350; obj* x_351; obj* x_352; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_348 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_350 = x_8;
} else {
 lean::inc(x_348);
 lean::dec(x_8);
 x_350 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_351 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_351 = x_350;
}
lean::cnstr_set(x_351, 0, x_348);
x_352 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_352, 0, x_351);
lean::cnstr_set(x_352, 1, x_9);
return x_352;
}
else
{
obj* x_353; obj* x_355; 
x_353 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 x_355 = x_8;
} else {
 lean::inc(x_353);
 lean::dec(x_8);
 x_355 = lean::box(0);
}
if (lean::obj_tag(x_353) == 0)
{
obj* x_357; 
lean::dec(x_355);
x_357 = lean::cnstr_get(x_353, 0);
lean::inc(x_357);
lean::dec(x_353);
x_6 = x_357;
x_7 = x_9;
goto _start;
}
else
{
obj* x_366; obj* x_369; obj* x_370; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_366 = lean::cnstr_get(x_353, 0);
lean::inc(x_366);
lean::dec(x_353);
if (lean::is_scalar(x_355)) {
 x_369 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_369 = x_355;
}
lean::cnstr_set(x_369, 0, x_366);
x_370 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_370, 0, x_369);
lean::cnstr_set(x_370, 1, x_9);
return x_370;
}
}
}
}
}
obj* _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___closed__1() {
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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::inc(x_1);
x_9 = l_lean_file__map_from__string(x_1);
lean::inc(x_1);
lean::inc(x_0);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_12, 2, x_9);
x_13 = l_lean_expander_builtin__transformers;
lean::inc(x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
lean::inc(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_4);
x_18 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___closed__1;
x_19 = l_lean_elaborator_mk__state(x_17, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_15);
lean::cnstr_set(x_21, 1, x_20);
lean::inc(x_4);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_5);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6(x_0, x_1, x_2, x_3, x_4, x_6, x_25, x_7);
return x_26;
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
x_58 = l_lean_expander_expand__bracketed__binder___main___closed__4;
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
obj* x_60; obj* x_63; obj* x_65; obj* x_69; obj* x_71; obj* x_72; 
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
lean::inc(x_2);
x_71 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_69, x_6);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_65);
lean::dec(x_63);
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
obj* x_89; obj* x_92; 
lean::dec(x_72);
x_89 = lean::cnstr_get(x_71, 1);
lean::inc(x_89);
lean::dec(x_71);
x_92 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(x_0, x_1, x_2, x_3, x_29, x_63, x_65, x_89);
return x_92;
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_3);
x_9 = l_io_prim_iterate___main___at_lean_run__frontend___spec__6(x_0, x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_3);
x_9 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__5(x_0, x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
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
 l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__4 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__4();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__6___closed__4);
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___closed__1();
lean::mark_persistent(l_io_prim_iterate__eio___at_lean_run__frontend___spec__5___closed__1);
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

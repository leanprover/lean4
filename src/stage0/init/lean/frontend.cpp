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
obj* l_io_prim_iterate__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4(obj*, obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__6;
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
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_lean_process__file___closed__1;
obj* l_lean_run__frontend___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_io_println___at_has__repr_has__eval___spec__1(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1(obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3(obj*, obj*, obj*, obj*);
extern obj* l_lean_options_mk;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3;
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__header(obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2(obj*, obj*, obj*);
obj* l_lean_elaborator_mk__state(obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
obj* l_io__of__except___at_lean_run__frontend___spec__1(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__5(obj*, obj*, obj*);
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
obj* l_io__of__except___at_lean_run__frontend___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
} else {
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_8 = x_7;
 lean::cnstr_set_tag(x_7, 1);
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_14 = x_1;
} else {
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_9);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1, obj* x_2) {
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
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__1___boxed), 3, 2);
lean::closure_set(x_45, 0, x_19);
lean::closure_set(x_45, 1, x_13);
x_46 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__1;
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
obj* x_66; obj* x_70; 
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_43);
lean::dec(x_26);
x_66 = lean::cnstr_get(x_55, 0);
lean::inc(x_66);
lean::dec(x_55);
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
x_75 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__3(x_0, x_1, x_74);
if (lean::obj_tag(x_75) == 0)
{
if (x_2 == 0)
{
obj* x_78; obj* x_80; obj* x_81; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
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
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
if (lean::is_scalar(x_80)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_80;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_78);
return x_87;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_3);
x_89 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_91 = x_75;
} else {
 lean::inc(x_89);
 lean::dec(x_75);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_16, 8);
lean::inc(x_92);
lean::dec(x_16);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_53);
lean::cnstr_set(x_95, 1, x_24);
x_96 = l_list_reverse___rarg(x_95);
if (lean::is_scalar(x_57)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_57;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_92);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
if (lean::is_scalar(x_91)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_91;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_89);
return x_99;
}
}
else
{
obj* x_105; obj* x_107; obj* x_109; obj* x_110; 
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_57);
lean::dec(x_53);
x_105 = lean::cnstr_get(x_75, 0);
x_107 = lean::cnstr_get(x_75, 1);
if (lean::is_exclusive(x_75)) {
 x_109 = x_75;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_75);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_105);
lean::cnstr_set(x_110, 1, x_107);
return x_110;
}
}
else
{
obj* x_118; obj* x_120; obj* x_122; obj* x_123; 
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_57);
lean::dec(x_53);
x_118 = lean::cnstr_get(x_70, 0);
x_120 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 x_122 = x_70;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::dec(x_70);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_118);
lean::cnstr_set(x_123, 1, x_120);
return x_123;
}
}
else
{
obj* x_125; obj* x_128; obj* x_130; obj* x_132; obj* x_133; obj* x_135; 
lean::dec(x_1);
x_125 = lean::cnstr_get(x_55, 0);
lean::inc(x_125);
lean::dec(x_55);
x_128 = lean::cnstr_get(x_125, 0);
x_130 = lean::cnstr_get(x_125, 1);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_set(x_125, 0, lean::box(0));
 lean::cnstr_set(x_125, 1, lean::box(0));
 x_132 = x_125;
} else {
 lean::inc(x_128);
 lean::inc(x_130);
 lean::dec(x_125);
 x_132 = lean::box(0);
}
x_133 = l_list_reverse___rarg(x_130);
lean::inc(x_0);
x_135 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__4(x_0, x_133, x_59);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_138; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_135, 1);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 x_138 = x_135;
} else {
 lean::inc(x_136);
 lean::dec(x_135);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_58);
lean::cnstr_set(x_139, 1, x_136);
lean::inc(x_22);
lean::inc(x_53);
x_142 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__2___boxed), 3, 2);
lean::closure_set(x_142, 0, x_53);
lean::closure_set(x_142, 1, x_22);
x_143 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__2;
x_144 = l_lean_profileit__pure___rarg(x_143, x_43, x_142, x_139);
if (lean::obj_tag(x_144) == 0)
{
obj* x_145; obj* x_147; obj* x_149; obj* x_150; 
x_145 = lean::cnstr_get(x_144, 0);
x_147 = lean::cnstr_get(x_144, 1);
if (lean::is_exclusive(x_144)) {
 x_149 = x_144;
} else {
 lean::inc(x_145);
 lean::inc(x_147);
 lean::dec(x_144);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_58);
lean::cnstr_set(x_150, 1, x_147);
if (lean::obj_tag(x_145) == 0)
{
lean::dec(x_4);
lean::dec(x_43);
if (x_2 == 0)
{
obj* x_155; obj* x_158; 
lean::dec(x_24);
lean::dec(x_53);
x_155 = lean::cnstr_get(x_145, 0);
lean::inc(x_155);
lean::dec(x_145);
x_158 = lean::apply_2(x_0, x_155, x_150);
if (lean::obj_tag(x_158) == 0)
{
obj* x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_159 = lean::cnstr_get(x_158, 1);
if (lean::is_exclusive(x_158)) {
 lean::cnstr_release(x_158, 0);
 x_161 = x_158;
} else {
 lean::inc(x_159);
 lean::dec(x_158);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_132;
}
lean::cnstr_set(x_162, 0, x_22);
lean::cnstr_set(x_162, 1, x_3);
if (lean::is_scalar(x_57)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_57;
}
lean::cnstr_set(x_163, 0, x_19);
lean::cnstr_set(x_163, 1, x_162);
if (lean::is_scalar(x_26)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_26;
}
lean::cnstr_set(x_164, 0, x_16);
lean::cnstr_set(x_164, 1, x_163);
if (lean::is_scalar(x_21)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_21;
}
lean::cnstr_set(x_165, 0, x_128);
lean::cnstr_set(x_165, 1, x_164);
x_166 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_166, 0, x_165);
if (lean::is_scalar(x_161)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_161;
}
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_159);
return x_167;
}
else
{
obj* x_177; obj* x_179; obj* x_181; obj* x_182; 
lean::dec(x_22);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_132);
lean::dec(x_128);
x_177 = lean::cnstr_get(x_158, 0);
x_179 = lean::cnstr_get(x_158, 1);
if (lean::is_exclusive(x_158)) {
 x_181 = x_158;
} else {
 lean::inc(x_177);
 lean::inc(x_179);
 lean::dec(x_158);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_177);
lean::cnstr_set(x_182, 1, x_179);
return x_182;
}
}
else
{
obj* x_184; obj* x_187; 
lean::dec(x_3);
x_184 = lean::cnstr_get(x_145, 0);
lean::inc(x_184);
lean::dec(x_145);
x_187 = lean::apply_2(x_0, x_184, x_150);
if (lean::obj_tag(x_187) == 0)
{
obj* x_188; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; 
x_188 = lean::cnstr_get(x_187, 1);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 x_190 = x_187;
} else {
 lean::inc(x_188);
 lean::dec(x_187);
 x_190 = lean::box(0);
}
x_191 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_191, 0, x_53);
lean::cnstr_set(x_191, 1, x_24);
if (lean::is_scalar(x_132)) {
 x_192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_192 = x_132;
}
lean::cnstr_set(x_192, 0, x_22);
lean::cnstr_set(x_192, 1, x_191);
if (lean::is_scalar(x_57)) {
 x_193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_193 = x_57;
}
lean::cnstr_set(x_193, 0, x_19);
lean::cnstr_set(x_193, 1, x_192);
if (lean::is_scalar(x_26)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_26;
}
lean::cnstr_set(x_194, 0, x_16);
lean::cnstr_set(x_194, 1, x_193);
if (lean::is_scalar(x_21)) {
 x_195 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_195 = x_21;
}
lean::cnstr_set(x_195, 0, x_128);
lean::cnstr_set(x_195, 1, x_194);
x_196 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_196, 0, x_195);
if (lean::is_scalar(x_190)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_190;
}
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_188);
return x_197;
}
else
{
obj* x_208; obj* x_210; obj* x_212; obj* x_213; 
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_16);
lean::dec(x_19);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_128);
x_208 = lean::cnstr_get(x_187, 0);
x_210 = lean::cnstr_get(x_187, 1);
if (lean::is_exclusive(x_187)) {
 x_212 = x_187;
} else {
 lean::inc(x_208);
 lean::inc(x_210);
 lean::dec(x_187);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_208);
lean::cnstr_set(x_213, 1, x_210);
return x_213;
}
}
}
else
{
obj* x_216; obj* x_220; obj* x_221; obj* x_222; 
lean::dec(x_22);
lean::dec(x_19);
x_216 = lean::cnstr_get(x_145, 0);
lean::inc(x_216);
lean::dec(x_145);
lean::inc(x_216);
x_220 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__3___boxed), 4, 3);
lean::closure_set(x_220, 0, x_4);
lean::closure_set(x_220, 1, x_16);
lean::closure_set(x_220, 2, x_216);
x_221 = l_io_prim_iterate___at_lean_run__frontend___spec__6___lambda__4___closed__3;
x_222 = l_lean_profileit__pure___rarg(x_221, x_43, x_220, x_150);
lean::dec(x_43);
if (lean::obj_tag(x_222) == 0)
{
obj* x_224; obj* x_226; obj* x_228; obj* x_229; obj* x_230; obj* x_232; obj* x_233; 
x_224 = lean::cnstr_get(x_222, 0);
x_226 = lean::cnstr_get(x_222, 1);
if (lean::is_exclusive(x_222)) {
 x_228 = x_222;
} else {
 lean::inc(x_224);
 lean::inc(x_226);
 lean::dec(x_222);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_58);
lean::cnstr_set(x_229, 1, x_226);
x_230 = lean::cnstr_get(x_224, 5);
lean::inc(x_230);
x_232 = l_list_reverse___rarg(x_230);
x_233 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__5(x_0, x_232, x_229);
if (lean::obj_tag(x_233) == 0)
{
obj* x_234; obj* x_236; obj* x_237; uint8 x_238; 
x_234 = lean::cnstr_get(x_233, 1);
if (lean::is_exclusive(x_233)) {
 lean::cnstr_release(x_233, 0);
 lean::cnstr_set(x_233, 1, lean::box(0));
 x_236 = x_233;
} else {
 lean::inc(x_234);
 lean::dec(x_233);
 x_236 = lean::box(0);
}
x_237 = l_lean_parser_module_eoi;
x_238 = l_lean_parser_syntax_is__of__kind___main(x_237, x_216);
lean::dec(x_216);
if (x_238 == 0)
{
if (x_2 == 0)
{
obj* x_242; obj* x_244; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_24);
lean::dec(x_53);
x_242 = lean::cnstr_get(x_224, 6);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_224, 7);
lean::inc(x_244);
if (lean::is_scalar(x_132)) {
 x_246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_246 = x_132;
}
lean::cnstr_set(x_246, 0, x_244);
lean::cnstr_set(x_246, 1, x_3);
if (lean::is_scalar(x_57)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_57;
}
lean::cnstr_set(x_247, 0, x_242);
lean::cnstr_set(x_247, 1, x_246);
if (lean::is_scalar(x_26)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_26;
}
lean::cnstr_set(x_248, 0, x_224);
lean::cnstr_set(x_248, 1, x_247);
if (lean::is_scalar(x_21)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_21;
}
lean::cnstr_set(x_249, 0, x_128);
lean::cnstr_set(x_249, 1, x_248);
x_250 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_250, 0, x_249);
if (lean::is_scalar(x_236)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_236;
}
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_234);
return x_251;
}
else
{
obj* x_253; obj* x_255; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_3);
x_253 = lean::cnstr_get(x_224, 6);
lean::inc(x_253);
x_255 = lean::cnstr_get(x_224, 7);
lean::inc(x_255);
x_257 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_257, 0, x_53);
lean::cnstr_set(x_257, 1, x_24);
if (lean::is_scalar(x_132)) {
 x_258 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_258 = x_132;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_257);
if (lean::is_scalar(x_57)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_57;
}
lean::cnstr_set(x_259, 0, x_253);
lean::cnstr_set(x_259, 1, x_258);
if (lean::is_scalar(x_26)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_26;
}
lean::cnstr_set(x_260, 0, x_224);
lean::cnstr_set(x_260, 1, x_259);
if (lean::is_scalar(x_21)) {
 x_261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_261 = x_21;
}
lean::cnstr_set(x_261, 0, x_128);
lean::cnstr_set(x_261, 1, x_260);
x_262 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_262, 0, x_261);
if (lean::is_scalar(x_236)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_236;
}
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_234);
return x_263;
}
}
else
{
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_128);
if (x_2 == 0)
{
obj* x_270; obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_24);
lean::dec(x_53);
x_270 = lean::cnstr_get(x_224, 8);
lean::inc(x_270);
lean::dec(x_224);
x_273 = l_list_reverse___rarg(x_3);
if (lean::is_scalar(x_132)) {
 x_274 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_274 = x_132;
}
lean::cnstr_set(x_274, 0, x_273);
lean::cnstr_set(x_274, 1, x_270);
x_275 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_275, 0, x_274);
if (lean::is_scalar(x_236)) {
 x_276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_276 = x_236;
}
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_234);
return x_276;
}
else
{
obj* x_278; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_3);
x_278 = lean::cnstr_get(x_224, 8);
lean::inc(x_278);
lean::dec(x_224);
x_281 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_281, 0, x_53);
lean::cnstr_set(x_281, 1, x_24);
x_282 = l_list_reverse___rarg(x_281);
if (lean::is_scalar(x_132)) {
 x_283 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_283 = x_132;
}
lean::cnstr_set(x_283, 0, x_282);
lean::cnstr_set(x_283, 1, x_278);
x_284 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_284, 0, x_283);
if (lean::is_scalar(x_236)) {
 x_285 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_285 = x_236;
}
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_234);
return x_285;
}
}
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; 
lean::dec(x_216);
lean::dec(x_224);
lean::dec(x_24);
lean::dec(x_3);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_128);
x_296 = lean::cnstr_get(x_233, 0);
x_298 = lean::cnstr_get(x_233, 1);
if (lean::is_exclusive(x_233)) {
 x_300 = x_233;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_233);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_296);
lean::cnstr_set(x_301, 1, x_298);
return x_301;
}
}
else
{
obj* x_312; obj* x_314; obj* x_316; obj* x_317; 
lean::dec(x_216);
lean::dec(x_24);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_57);
lean::dec(x_26);
lean::dec(x_53);
lean::dec(x_132);
lean::dec(x_128);
x_312 = lean::cnstr_get(x_222, 0);
x_314 = lean::cnstr_get(x_222, 1);
if (lean::is_exclusive(x_222)) {
 x_316 = x_222;
} else {
 lean::inc(x_312);
 lean::inc(x_314);
 lean::dec(x_222);
 x_316 = lean::box(0);
}
if (lean::is_scalar(x_316)) {
 x_317 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_317 = x_316;
}
lean::cnstr_set(x_317, 0, x_312);
lean::cnstr_set(x_317, 1, x_314);
return x_317;
}
}
}
else
{
obj* x_332; obj* x_334; obj* x_336; obj* x_337; 
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
lean::dec(x_128);
x_332 = lean::cnstr_get(x_144, 0);
x_334 = lean::cnstr_get(x_144, 1);
if (lean::is_exclusive(x_144)) {
 x_336 = x_144;
} else {
 lean::inc(x_332);
 lean::inc(x_334);
 lean::dec(x_144);
 x_336 = lean::box(0);
}
if (lean::is_scalar(x_336)) {
 x_337 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_337 = x_336;
}
lean::cnstr_set(x_337, 0, x_332);
lean::cnstr_set(x_337, 1, x_334);
return x_337;
}
}
else
{
obj* x_352; obj* x_354; obj* x_356; obj* x_357; 
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
lean::dec(x_128);
x_352 = lean::cnstr_get(x_135, 0);
x_354 = lean::cnstr_get(x_135, 1);
if (lean::is_exclusive(x_135)) {
 x_356 = x_135;
} else {
 lean::inc(x_352);
 lean::inc(x_354);
 lean::dec(x_135);
 x_356 = lean::box(0);
}
if (lean::is_scalar(x_356)) {
 x_357 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_357 = x_356;
}
lean::cnstr_set(x_357, 0, x_352);
lean::cnstr_set(x_357, 1, x_354);
return x_357;
}
}
}
else
{
obj* x_369; obj* x_371; obj* x_373; obj* x_374; 
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
x_369 = lean::cnstr_get(x_47, 0);
x_371 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_373 = x_47;
} else {
 lean::inc(x_369);
 lean::inc(x_371);
 lean::dec(x_47);
 x_373 = lean::box(0);
}
if (lean::is_scalar(x_373)) {
 x_374 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_374 = x_373;
}
lean::cnstr_set(x_374, 0, x_369);
lean::cnstr_set(x_374, 1, x_371);
return x_374;
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
obj* x_8; obj* x_9; 
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_lean_mk__config(x_0, x_1);
x_9 = l_io__of__except___at_lean_run__frontend___spec__1(x_8, x_5);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_14 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_parse__header(x_10);
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::box(0);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_12);
if (lean::obj_tag(x_17) == 0)
{
obj* x_25; obj* x_28; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = lean::apply_2(x_2, x_25, x_21);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 x_31 = x_28;
} else {
 lean::inc(x_29);
 lean::dec(x_28);
 x_31 = lean::box(0);
}
x_32 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_19;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_4);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_29);
return x_34;
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; 
lean::dec(x_4);
lean::dec(x_19);
x_37 = lean::cnstr_get(x_28, 0);
x_39 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_41 = x_28;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_28);
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
else
{
obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_54; 
x_43 = lean::cnstr_get(x_17, 0);
lean::inc(x_43);
lean::dec(x_17);
x_46 = lean::cnstr_get(x_43, 0);
x_48 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_set(x_43, 0, lean::box(0));
 lean::cnstr_set(x_43, 1, lean::box(0));
 x_50 = x_43;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_43);
 x_50 = lean::box(0);
}
x_51 = l_list_reverse___rarg(x_48);
lean::inc(x_51);
lean::inc(x_2);
x_54 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__2(x_2, x_51, x_21);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_55 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_57 = x_54;
} else {
 lean::inc(x_55);
 lean::dec(x_54);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_20);
lean::cnstr_set(x_58, 1, x_55);
x_59 = lean::cnstr_get(x_10, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
lean::dec(x_59);
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_expander_builtin__transformers;
lean::inc(x_64);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_67);
x_70 = lean::cnstr_get(x_64, 2);
lean::inc(x_70);
lean::dec(x_64);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_0);
lean::cnstr_set(x_73, 1, x_1);
lean::cnstr_set(x_73, 2, x_70);
lean::inc(x_10);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_10);
x_76 = l_lean_run__frontend___closed__1;
lean::inc(x_75);
x_78 = l_lean_elaborator_mk__state(x_75, x_4, x_76);
x_79 = lean::box(0);
if (lean::is_scalar(x_50)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_50;
}
lean::cnstr_set(x_80, 0, x_69);
lean::cnstr_set(x_80, 1, x_79);
if (lean::is_scalar(x_19)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_19;
}
lean::cnstr_set(x_81, 0, x_10);
lean::cnstr_set(x_81, 1, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_46);
lean::cnstr_set(x_83, 1, x_82);
x_84 = l_io_prim_iterate___at_lean_run__frontend___spec__6(x_2, x_3, x_51, x_75, x_79, x_83, x_58);
return x_84;
}
else
{
obj* x_94; obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_50);
lean::dec(x_51);
lean::dec(x_19);
lean::dec(x_46);
x_94 = lean::cnstr_get(x_54, 0);
x_96 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_98 = x_54;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_54);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_94);
lean::cnstr_set(x_99, 1, x_96);
return x_99;
}
}
}
else
{
obj* x_104; obj* x_106; obj* x_108; obj* x_109; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_104 = lean::cnstr_get(x_9, 0);
x_106 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_108 = x_9;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_9);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_104);
lean::cnstr_set(x_109, 1, x_106);
return x_109;
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
obj* l_lean_run__frontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
x_7 = l_lean_run__frontend(x_0, x_1, x_2, x_6, x_4, x_5);
return x_7;
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
x_4 = l_io_println___at_has__repr_has__eval___spec__1(x_3, x_2);
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
x_44 = l_io_println___at_has__repr_has__eval___spec__1(x_43, x_2);
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
x_58 = l_io_println___at_has__repr_has__eval___spec__1(x_57, x_2);
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
x_72 = l_io_println___at_has__repr_has__eval___spec__1(x_71, x_2);
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
obj* lean_process_file(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_9; 
x_5 = lean::box(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = 0;
lean::inc(x_0);
x_9 = l_lean_run__frontend(x_0, x_1, x_6, x_7, x_3, x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_11 = lean::cnstr_get(x_9, 0);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_15 = x_9;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
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
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_9, 0);
x_24 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_26 = x_9;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_9);
 x_26 = lean::box(0);
}
x_27 = lean::box(0);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_26;
 lean::cnstr_set_tag(x_26, 0);
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
if (x_2 == 0)
{
obj* x_29; obj* x_30; uint8 x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_29 = lean::box(0);
x_30 = l_lean_elaborator_notation_elaborate___closed__1;
x_31 = 2;
x_32 = l_string_iterator_extract___main___closed__1;
lean::inc(x_22);
x_34 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_34, 0, x_0);
lean::cnstr_set(x_34, 1, x_30);
lean::cnstr_set(x_34, 2, x_29);
lean::cnstr_set(x_34, 3, x_32);
lean::cnstr_set(x_34, 4, x_22);
lean::cnstr_set_scalar(x_34, sizeof(void*)*5, x_31);
x_35 = x_34;
x_36 = l_lean_message_to__string(x_35);
x_37 = l_io_println___at_has__repr_has__eval___spec__1(x_36, x_28);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; 
x_39 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_41 = x_37;
} else {
 lean::inc(x_39);
 lean::dec(x_37);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
 lean::cnstr_set_tag(x_41, 1);
}
lean::cnstr_set(x_42, 0, x_22);
lean::cnstr_set(x_42, 1, x_39);
return x_42;
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_22);
x_44 = lean::cnstr_get(x_37, 0);
x_46 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_48 = x_37;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_37);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_0);
lean::inc(x_22);
x_52 = l_string_quote(x_22);
x_53 = l_lean_process__file___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_lean_process__file___lambda__1___closed__7;
x_57 = lean::string_append(x_54, x_56);
x_58 = l_io_println___at_has__repr_has__eval___spec__1(x_57, x_28);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
x_60 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_62 = x_58;
} else {
 lean::inc(x_60);
 lean::dec(x_58);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_62;
 lean::cnstr_set_tag(x_62, 1);
}
lean::cnstr_set(x_63, 0, x_22);
lean::cnstr_set(x_63, 1, x_60);
return x_63;
}
else
{
obj* x_65; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_22);
x_65 = lean::cnstr_get(x_58, 0);
x_67 = lean::cnstr_get(x_58, 1);
if (lean::is_exclusive(x_58)) {
 x_69 = x_58;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_58);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_65);
lean::cnstr_set(x_70, 1, x_67);
return x_70;
}
}
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
obj* l_lean_process__file___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = lean_process_file(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_parser_module(obj*);
obj* initialize_init_lean_expander(obj*);
obj* initialize_init_lean_elaborator(obj*);
obj* initialize_init_lean_util(obj*);
obj* initialize_init_io(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_frontend(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_expander(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_util(w);
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
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
return w;
}

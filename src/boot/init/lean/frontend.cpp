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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed(obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_lean_parser_module_tokens;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___boxed(obj*, obj*);
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__6;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(obj*, obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_string_quote(obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_lean_process__file___closed__1;
obj* l_io_println___at_lean_run__frontend___spec__3___boxed(obj*, obj*);
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj*, obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1;
obj* l_lean_elaborator_run(obj*);
extern obj* l_lean_message__log_empty;
extern obj* l_lean_format_be___main___closed__1;
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14(obj*, obj*, obj*);
extern obj* l_lean_parser_run___rarg___closed__1;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l_lean_file__map_from__string(obj*);
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_reader__t_monad___rarg___lambda__9___boxed(obj*, obj*, obj*);
obj* l_io_print___at_lean_run__frontend___spec__4(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_io_println___at_lean_run__frontend___spec__3(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2;
obj* l_io_print___at_lean_run__frontend___spec__4___boxed(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1(obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5___boxed(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_lean_profileit__pure___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__4;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3;
obj* l_lean_mk__config(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = l_lean_parser_module_tokens;
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
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
} else {
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
if (lean::is_scalar(x_5)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_5;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_14 = x_0;
} else {
 lean::inc(x_12);
 lean::dec(x_0);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_15);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_20, 0, x_19);
return x_20;
}
}
}
obj* _init_l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::string_mk_iterator(x_1);
x_5 = lean::apply_2(x_0, x_4, x_3);
x_6 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_release(x_1, 1);
 x_4 = x_1;
} else {
 lean::inc(x_2);
 lean::dec(x_1);
 x_4 = lean::box(0);
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 3);
lean::inc(x_8);
x_10 = l_option_get___main___at_lean_parser_run___spec__2(x_8);
lean::dec(x_8);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_10);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_lean_parser_message__of__parsec__message___rarg(x_19, x_5);
x_23 = l_lean_message__log_empty;
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
if (lean::is_scalar(x_4)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_4;
}
lean::cnstr_set(x_25, 0, x_12);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_4);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_2, 0);
lean::inc(x_29);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_29, 0);
x_34 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 x_36 = x_29;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_29);
 x_36 = lean::box(0);
}
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_32);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_39, 0, x_38);
return x_39;
}
}
}
obj* l_lean_parser_run___at_lean_run__frontend___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_3 = l_lean_message__log_empty;
lean::inc(x_0);
x_5 = lean::apply_2(x_2, x_3, x_0);
x_6 = l_string_join___closed__1;
x_7 = l_lean_parser_run___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(x_5, x_1, x_6, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1), 2, 1);
lean::closure_set(x_9, 0, x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
return x_10;
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
obj* _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_expander_expand(x_3, x_1);
return x_6;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parser died!!");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborator died!!");
return x_0;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_6, 0);
lean::inc(x_15);
lean::dec(x_6);
x_18 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_release(x_8, 1);
 x_20 = x_8;
} else {
 lean::inc(x_18);
 lean::dec(x_8);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_10, 0);
x_23 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_25 = x_10;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_10);
 x_25 = lean::box(0);
}
lean::inc(x_18);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_27, 0, x_12);
lean::closure_set(x_27, 1, x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; 
x_30 = l_lean_elaborator_notation_elaborate___closed__1;
x_28 = x_30;
goto lbl_29;
}
else
{
obj* x_31; obj* x_33; 
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_31, 3);
lean::inc(x_33);
lean::dec(x_31);
x_28 = x_33;
goto lbl_29;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_37 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_39 = x_3;
} else {
 lean::inc(x_37);
 lean::dec(x_3);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_4);
return x_41;
}
else
{
obj* x_42; obj* x_44; 
x_42 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_44 = x_3;
} else {
 lean::inc(x_42);
 lean::dec(x_3);
 x_44 = lean::box(0);
}
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; 
lean::dec(x_44);
x_46 = lean::cnstr_get(x_42, 0);
lean::inc(x_46);
lean::dec(x_42);
x_1 = x_46;
x_2 = x_4;
goto _start;
}
else
{
obj* x_51; obj* x_54; obj* x_55; 
lean::dec(x_0);
x_51 = lean::cnstr_get(x_42, 0);
lean::inc(x_51);
lean::dec(x_42);
if (lean::is_scalar(x_44)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_44;
}
lean::cnstr_set(x_54, 0, x_51);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_4);
return x_55;
}
}
}
lbl_29:
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1;
x_57 = l_lean_profileit__pure___rarg(x_56, x_28, x_27, x_2);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_67; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_15);
lean::dec(x_20);
lean::dec(x_25);
lean::dec(x_28);
lean::dec(x_58);
x_67 = lean::cnstr_get(x_57, 1);
lean::inc(x_67);
lean::dec(x_57);
x_70 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2;
x_71 = l_io_println___at_lean_run__frontend___spec__3(x_70, x_67);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_23);
x_75 = lean::cnstr_get(x_71, 1);
lean::inc(x_75);
lean::dec(x_71);
x_78 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_80 = x_72;
} else {
 lean::inc(x_78);
 lean::dec(x_72);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
x_3 = x_81;
x_4 = x_75;
goto lbl_5;
}
else
{
obj* x_82; obj* x_83; obj* x_86; obj* x_87; obj* x_88; 
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 x_82 = x_72;
} else {
 lean::dec(x_72);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_71, 1);
lean::inc(x_83);
lean::dec(x_71);
x_86 = l_list_reverse___rarg(x_23);
x_87 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
if (lean::is_scalar(x_82)) {
 x_88 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_88 = x_82;
}
lean::cnstr_set(x_88, 0, x_87);
x_3 = x_88;
x_4 = x_83;
goto lbl_5;
}
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_97; obj* x_99; obj* x_101; 
x_89 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_set(x_57, 1, lean::box(0));
 x_91 = x_57;
} else {
 lean::inc(x_89);
 lean::dec(x_57);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_58, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_58, 1);
lean::inc(x_94);
lean::dec(x_58);
x_99 = lean::cnstr_get(x_92, 1);
lean::inc(x_99);
x_101 = l_list_reverse___rarg(x_99);
if (lean::obj_tag(x_101) == 0)
{
obj* x_103; 
lean::dec(x_20);
x_103 = lean::box(0);
x_97 = x_103;
goto lbl_98;
}
else
{
obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_25);
lean::dec(x_91);
lean::inc(x_101);
lean::inc(x_0);
x_108 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_101, x_89);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_109 = x_101;
} else {
 lean::dec(x_101);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_108, 0);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_121; obj* x_124; obj* x_126; obj* x_127; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_15);
lean::dec(x_20);
lean::dec(x_23);
lean::dec(x_92);
lean::dec(x_94);
lean::dec(x_28);
lean::dec(x_109);
x_121 = lean::cnstr_get(x_108, 1);
lean::inc(x_121);
lean::dec(x_108);
x_124 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_126 = x_110;
} else {
 lean::inc(x_124);
 lean::dec(x_110);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
x_3 = x_127;
x_4 = x_121;
goto lbl_5;
}
else
{
obj* x_129; obj* x_131; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_110);
x_129 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 lean::cnstr_set(x_108, 1, lean::box(0));
 x_131 = x_108;
} else {
 lean::inc(x_129);
 lean::dec(x_108);
 x_131 = lean::box(0);
}
lean::inc(x_21);
lean::inc(x_92);
x_134 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1___boxed), 3, 2);
lean::closure_set(x_134, 0, x_92);
lean::closure_set(x_134, 1, x_21);
x_135 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3;
x_136 = l_lean_profileit__pure___rarg(x_135, x_28, x_134, x_129);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_140; obj* x_142; obj* x_143; obj* x_147; obj* x_148; 
lean::dec(x_28);
x_140 = lean::cnstr_get(x_136, 1);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_set(x_136, 1, lean::box(0));
 x_142 = x_136;
} else {
 lean::inc(x_140);
 lean::dec(x_136);
 x_142 = lean::box(0);
}
x_143 = lean::cnstr_get(x_137, 0);
lean::inc(x_143);
lean::dec(x_137);
lean::inc(x_0);
x_147 = lean::apply_2(x_0, x_143, x_140);
x_148 = lean::cnstr_get(x_147, 0);
lean::inc(x_148);
if (lean::obj_tag(x_148) == 0)
{
obj* x_160; obj* x_163; obj* x_165; obj* x_166; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_15);
lean::dec(x_20);
lean::dec(x_23);
lean::dec(x_92);
lean::dec(x_94);
lean::dec(x_109);
lean::dec(x_131);
lean::dec(x_142);
x_160 = lean::cnstr_get(x_147, 1);
lean::inc(x_160);
lean::dec(x_147);
x_163 = lean::cnstr_get(x_148, 0);
if (lean::is_exclusive(x_148)) {
 x_165 = x_148;
} else {
 lean::inc(x_163);
 lean::dec(x_148);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_163);
x_3 = x_166;
x_4 = x_160;
goto lbl_5;
}
else
{
obj* x_167; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
if (lean::is_exclusive(x_148)) {
 lean::cnstr_release(x_148, 0);
 x_167 = x_148;
} else {
 lean::dec(x_148);
 x_167 = lean::box(0);
}
x_168 = lean::cnstr_get(x_147, 1);
if (lean::is_exclusive(x_147)) {
 lean::cnstr_release(x_147, 0);
 x_170 = x_147;
} else {
 lean::inc(x_168);
 lean::dec(x_147);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_171 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_171 = x_109;
}
lean::cnstr_set(x_171, 0, x_92);
lean::cnstr_set(x_171, 1, x_23);
if (lean::is_scalar(x_170)) {
 x_172 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_172 = x_170;
}
lean::cnstr_set(x_172, 0, x_21);
lean::cnstr_set(x_172, 1, x_171);
if (lean::is_scalar(x_142)) {
 x_173 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_173 = x_142;
}
lean::cnstr_set(x_173, 0, x_18);
lean::cnstr_set(x_173, 1, x_172);
if (lean::is_scalar(x_131)) {
 x_174 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_174 = x_131;
}
lean::cnstr_set(x_174, 0, x_15);
lean::cnstr_set(x_174, 1, x_173);
if (lean::is_scalar(x_20)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_20;
}
lean::cnstr_set(x_175, 0, x_94);
lean::cnstr_set(x_175, 1, x_174);
x_176 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_176, 0, x_175);
if (lean::is_scalar(x_167)) {
 x_177 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_177 = x_167;
}
lean::cnstr_set(x_177, 0, x_176);
x_3 = x_177;
x_4 = x_168;
goto lbl_5;
}
}
else
{
obj* x_181; obj* x_183; obj* x_184; obj* x_188; obj* x_189; obj* x_190; obj* x_192; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_20);
x_181 = lean::cnstr_get(x_136, 1);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_set(x_136, 1, lean::box(0));
 x_183 = x_136;
} else {
 lean::inc(x_181);
 lean::dec(x_136);
 x_183 = lean::box(0);
}
x_184 = lean::cnstr_get(x_137, 0);
lean::inc(x_184);
lean::dec(x_137);
lean::inc(x_184);
x_188 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_188, 0, x_15);
lean::closure_set(x_188, 1, x_184);
x_189 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4;
x_190 = l_lean_profileit__pure___rarg(x_189, x_28, x_188, x_181);
lean::dec(x_28);
x_192 = lean::cnstr_get(x_190, 0);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_197; obj* x_200; obj* x_203; obj* x_205; uint8 x_206; 
lean::dec(x_94);
lean::dec(x_183);
lean::dec(x_131);
x_197 = lean::cnstr_get(x_190, 1);
lean::inc(x_197);
lean::dec(x_190);
x_200 = lean::cnstr_get(x_192, 0);
lean::inc(x_200);
lean::dec(x_192);
x_205 = l_lean_parser_module_eoi;
x_206 = l_lean_parser_syntax_is__of__kind___main(x_205, x_184);
lean::dec(x_184);
if (x_206 == 0)
{
obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_109);
x_209 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
x_210 = l_io_println___at_lean_run__frontend___spec__3(x_209, x_197);
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
if (lean::obj_tag(x_211) == 0)
{
obj* x_216; obj* x_219; obj* x_221; obj* x_222; 
lean::dec(x_200);
lean::dec(x_23);
lean::dec(x_92);
x_216 = lean::cnstr_get(x_210, 1);
lean::inc(x_216);
lean::dec(x_210);
x_219 = lean::cnstr_get(x_211, 0);
if (lean::is_exclusive(x_211)) {
 x_221 = x_211;
} else {
 lean::inc(x_219);
 lean::dec(x_211);
 x_221 = lean::box(0);
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_219);
x_3 = x_222;
x_4 = x_216;
goto lbl_5;
}
else
{
obj* x_224; obj* x_227; obj* x_229; obj* x_230; 
lean::dec(x_211);
x_224 = lean::cnstr_get(x_210, 1);
lean::inc(x_224);
lean::dec(x_210);
x_227 = l_list_reverse___rarg(x_200);
lean::inc(x_0);
x_229 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_227, x_224);
x_230 = lean::cnstr_get(x_229, 0);
lean::inc(x_230);
if (lean::obj_tag(x_230) == 0)
{
obj* x_234; obj* x_237; obj* x_239; obj* x_240; 
lean::dec(x_23);
lean::dec(x_92);
x_234 = lean::cnstr_get(x_229, 1);
lean::inc(x_234);
lean::dec(x_229);
x_237 = lean::cnstr_get(x_230, 0);
if (lean::is_exclusive(x_230)) {
 x_239 = x_230;
} else {
 lean::inc(x_237);
 lean::dec(x_230);
 x_239 = lean::box(0);
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_237);
x_3 = x_240;
x_4 = x_234;
goto lbl_5;
}
else
{
obj* x_241; obj* x_242; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
if (lean::is_exclusive(x_230)) {
 lean::cnstr_release(x_230, 0);
 x_241 = x_230;
} else {
 lean::dec(x_230);
 x_241 = lean::box(0);
}
x_242 = lean::cnstr_get(x_229, 1);
lean::inc(x_242);
lean::dec(x_229);
x_245 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_245, 0, x_92);
lean::cnstr_set(x_245, 1, x_23);
x_246 = l_list_reverse___rarg(x_245);
x_247 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_247, 0, x_246);
if (lean::is_scalar(x_241)) {
 x_248 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_248 = x_241;
}
lean::cnstr_set(x_248, 0, x_247);
x_3 = x_248;
x_4 = x_242;
goto lbl_5;
}
}
}
else
{
obj* x_249; 
x_249 = lean::box(0);
x_203 = x_249;
goto lbl_204;
}
lbl_204:
{
obj* x_251; obj* x_253; obj* x_254; 
lean::dec(x_203);
x_251 = l_list_reverse___rarg(x_200);
lean::inc(x_0);
x_253 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_251, x_197);
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
if (lean::obj_tag(x_254) == 0)
{
obj* x_259; obj* x_262; obj* x_264; obj* x_265; 
lean::dec(x_23);
lean::dec(x_92);
lean::dec(x_109);
x_259 = lean::cnstr_get(x_253, 1);
lean::inc(x_259);
lean::dec(x_253);
x_262 = lean::cnstr_get(x_254, 0);
if (lean::is_exclusive(x_254)) {
 x_264 = x_254;
} else {
 lean::inc(x_262);
 lean::dec(x_254);
 x_264 = lean::box(0);
}
if (lean::is_scalar(x_264)) {
 x_265 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_265 = x_264;
}
lean::cnstr_set(x_265, 0, x_262);
x_3 = x_265;
x_4 = x_259;
goto lbl_5;
}
else
{
obj* x_266; obj* x_267; obj* x_270; obj* x_271; obj* x_272; obj* x_273; 
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 x_266 = x_254;
} else {
 lean::dec(x_254);
 x_266 = lean::box(0);
}
x_267 = lean::cnstr_get(x_253, 1);
lean::inc(x_267);
lean::dec(x_253);
if (lean::is_scalar(x_109)) {
 x_270 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_270 = x_109;
}
lean::cnstr_set(x_270, 0, x_92);
lean::cnstr_set(x_270, 1, x_23);
x_271 = l_list_reverse___rarg(x_270);
x_272 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_272, 0, x_271);
if (lean::is_scalar(x_266)) {
 x_273 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_273 = x_266;
}
lean::cnstr_set(x_273, 0, x_272);
x_3 = x_273;
x_4 = x_267;
goto lbl_5;
}
}
}
else
{
obj* x_275; obj* x_277; obj* x_278; obj* x_280; obj* x_283; obj* x_285; obj* x_287; obj* x_288; 
lean::dec(x_184);
x_275 = lean::cnstr_get(x_190, 1);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_set(x_190, 1, lean::box(0));
 x_277 = x_190;
} else {
 lean::inc(x_275);
 lean::dec(x_190);
 x_277 = lean::box(0);
}
x_278 = lean::cnstr_get(x_192, 0);
lean::inc(x_278);
x_280 = lean::cnstr_get(x_192, 1);
lean::inc(x_280);
lean::dec(x_192);
x_283 = lean::cnstr_get(x_278, 5);
lean::inc(x_283);
x_285 = l_list_reverse___rarg(x_283);
lean::inc(x_0);
x_287 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_285, x_275);
x_288 = lean::cnstr_get(x_287, 0);
lean::inc(x_288);
if (lean::obj_tag(x_288) == 0)
{
obj* x_299; obj* x_302; obj* x_304; obj* x_305; 
lean::dec(x_280);
lean::dec(x_278);
lean::dec(x_277);
lean::dec(x_23);
lean::dec(x_92);
lean::dec(x_94);
lean::dec(x_183);
lean::dec(x_109);
lean::dec(x_131);
x_299 = lean::cnstr_get(x_287, 1);
lean::inc(x_299);
lean::dec(x_287);
x_302 = lean::cnstr_get(x_288, 0);
if (lean::is_exclusive(x_288)) {
 x_304 = x_288;
} else {
 lean::inc(x_302);
 lean::dec(x_288);
 x_304 = lean::box(0);
}
if (lean::is_scalar(x_304)) {
 x_305 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_305 = x_304;
}
lean::cnstr_set(x_305, 0, x_302);
x_3 = x_305;
x_4 = x_299;
goto lbl_5;
}
else
{
obj* x_306; obj* x_307; obj* x_309; obj* x_310; obj* x_312; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; 
if (lean::is_exclusive(x_288)) {
 lean::cnstr_release(x_288, 0);
 x_306 = x_288;
} else {
 lean::dec(x_288);
 x_306 = lean::box(0);
}
x_307 = lean::cnstr_get(x_287, 1);
if (lean::is_exclusive(x_287)) {
 lean::cnstr_release(x_287, 0);
 x_309 = x_287;
} else {
 lean::inc(x_307);
 lean::dec(x_287);
 x_309 = lean::box(0);
}
x_310 = lean::cnstr_get(x_278, 6);
lean::inc(x_310);
x_312 = lean::cnstr_get(x_278, 7);
lean::inc(x_312);
lean::dec(x_278);
if (lean::is_scalar(x_109)) {
 x_315 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_315 = x_109;
}
lean::cnstr_set(x_315, 0, x_92);
lean::cnstr_set(x_315, 1, x_23);
if (lean::is_scalar(x_309)) {
 x_316 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_316 = x_309;
}
lean::cnstr_set(x_316, 0, x_312);
lean::cnstr_set(x_316, 1, x_315);
if (lean::is_scalar(x_277)) {
 x_317 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_317 = x_277;
}
lean::cnstr_set(x_317, 0, x_310);
lean::cnstr_set(x_317, 1, x_316);
if (lean::is_scalar(x_183)) {
 x_318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_318 = x_183;
}
lean::cnstr_set(x_318, 0, x_280);
lean::cnstr_set(x_318, 1, x_317);
if (lean::is_scalar(x_131)) {
 x_319 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_319 = x_131;
}
lean::cnstr_set(x_319, 0, x_94);
lean::cnstr_set(x_319, 1, x_318);
x_320 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_320, 0, x_319);
if (lean::is_scalar(x_306)) {
 x_321 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_321 = x_306;
}
lean::cnstr_set(x_321, 0, x_320);
x_3 = x_321;
x_4 = x_307;
goto lbl_5;
}
}
}
}
}
lbl_98:
{
obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
lean::dec(x_97);
lean::inc(x_21);
lean::inc(x_92);
x_325 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1___boxed), 3, 2);
lean::closure_set(x_325, 0, x_92);
lean::closure_set(x_325, 1, x_21);
x_326 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3;
x_327 = l_lean_profileit__pure___rarg(x_326, x_28, x_325, x_89);
x_328 = lean::cnstr_get(x_327, 0);
lean::inc(x_328);
if (lean::obj_tag(x_328) == 0)
{
obj* x_331; obj* x_333; obj* x_334; obj* x_338; obj* x_339; 
lean::dec(x_28);
x_331 = lean::cnstr_get(x_327, 1);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_set(x_327, 1, lean::box(0));
 x_333 = x_327;
} else {
 lean::inc(x_331);
 lean::dec(x_327);
 x_333 = lean::box(0);
}
x_334 = lean::cnstr_get(x_328, 0);
lean::inc(x_334);
lean::dec(x_328);
lean::inc(x_0);
x_338 = lean::apply_2(x_0, x_334, x_331);
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
if (lean::obj_tag(x_339) == 0)
{
obj* x_350; obj* x_353; obj* x_355; obj* x_356; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_15);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_92);
lean::dec(x_91);
lean::dec(x_333);
lean::dec(x_94);
x_350 = lean::cnstr_get(x_338, 1);
lean::inc(x_350);
lean::dec(x_338);
x_353 = lean::cnstr_get(x_339, 0);
if (lean::is_exclusive(x_339)) {
 x_355 = x_339;
} else {
 lean::inc(x_353);
 lean::dec(x_339);
 x_355 = lean::box(0);
}
if (lean::is_scalar(x_355)) {
 x_356 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_356 = x_355;
}
lean::cnstr_set(x_356, 0, x_353);
x_3 = x_356;
x_4 = x_350;
goto lbl_5;
}
else
{
obj* x_357; obj* x_358; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; 
if (lean::is_exclusive(x_339)) {
 lean::cnstr_release(x_339, 0);
 x_357 = x_339;
} else {
 lean::dec(x_339);
 x_357 = lean::box(0);
}
x_358 = lean::cnstr_get(x_338, 1);
if (lean::is_exclusive(x_338)) {
 lean::cnstr_release(x_338, 0);
 x_360 = x_338;
} else {
 lean::inc(x_358);
 lean::dec(x_338);
 x_360 = lean::box(0);
}
x_361 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_361, 0, x_92);
lean::cnstr_set(x_361, 1, x_23);
if (lean::is_scalar(x_360)) {
 x_362 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_362 = x_360;
}
lean::cnstr_set(x_362, 0, x_21);
lean::cnstr_set(x_362, 1, x_361);
if (lean::is_scalar(x_333)) {
 x_363 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_363 = x_333;
}
lean::cnstr_set(x_363, 0, x_18);
lean::cnstr_set(x_363, 1, x_362);
if (lean::is_scalar(x_91)) {
 x_364 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_364 = x_91;
}
lean::cnstr_set(x_364, 0, x_15);
lean::cnstr_set(x_364, 1, x_363);
if (lean::is_scalar(x_25)) {
 x_365 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_365 = x_25;
}
lean::cnstr_set(x_365, 0, x_94);
lean::cnstr_set(x_365, 1, x_364);
x_366 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_366, 0, x_365);
if (lean::is_scalar(x_357)) {
 x_367 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_367 = x_357;
}
lean::cnstr_set(x_367, 0, x_366);
x_3 = x_367;
x_4 = x_358;
goto lbl_5;
}
}
else
{
obj* x_371; obj* x_373; obj* x_374; obj* x_378; obj* x_379; obj* x_380; obj* x_382; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_25);
x_371 = lean::cnstr_get(x_327, 1);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 lean::cnstr_set(x_327, 1, lean::box(0));
 x_373 = x_327;
} else {
 lean::inc(x_371);
 lean::dec(x_327);
 x_373 = lean::box(0);
}
x_374 = lean::cnstr_get(x_328, 0);
lean::inc(x_374);
lean::dec(x_328);
lean::inc(x_374);
x_378 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_378, 0, x_15);
lean::closure_set(x_378, 1, x_374);
x_379 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4;
x_380 = l_lean_profileit__pure___rarg(x_379, x_28, x_378, x_371);
lean::dec(x_28);
x_382 = lean::cnstr_get(x_380, 0);
lean::inc(x_382);
if (lean::obj_tag(x_382) == 0)
{
obj* x_387; obj* x_390; obj* x_393; obj* x_395; uint8 x_396; 
lean::dec(x_91);
lean::dec(x_94);
lean::dec(x_373);
x_387 = lean::cnstr_get(x_380, 1);
lean::inc(x_387);
lean::dec(x_380);
x_390 = lean::cnstr_get(x_382, 0);
lean::inc(x_390);
lean::dec(x_382);
x_395 = l_lean_parser_module_eoi;
x_396 = l_lean_parser_syntax_is__of__kind___main(x_395, x_374);
lean::dec(x_374);
if (x_396 == 0)
{
obj* x_398; obj* x_399; obj* x_400; 
x_398 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
x_399 = l_io_println___at_lean_run__frontend___spec__3(x_398, x_387);
x_400 = lean::cnstr_get(x_399, 0);
lean::inc(x_400);
if (lean::obj_tag(x_400) == 0)
{
obj* x_405; obj* x_408; obj* x_410; obj* x_411; 
lean::dec(x_23);
lean::dec(x_92);
lean::dec(x_390);
x_405 = lean::cnstr_get(x_399, 1);
lean::inc(x_405);
lean::dec(x_399);
x_408 = lean::cnstr_get(x_400, 0);
if (lean::is_exclusive(x_400)) {
 x_410 = x_400;
} else {
 lean::inc(x_408);
 lean::dec(x_400);
 x_410 = lean::box(0);
}
if (lean::is_scalar(x_410)) {
 x_411 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_411 = x_410;
}
lean::cnstr_set(x_411, 0, x_408);
x_3 = x_411;
x_4 = x_405;
goto lbl_5;
}
else
{
obj* x_413; obj* x_416; obj* x_418; obj* x_419; 
lean::dec(x_400);
x_413 = lean::cnstr_get(x_399, 1);
lean::inc(x_413);
lean::dec(x_399);
x_416 = l_list_reverse___rarg(x_390);
lean::inc(x_0);
x_418 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_416, x_413);
x_419 = lean::cnstr_get(x_418, 0);
lean::inc(x_419);
if (lean::obj_tag(x_419) == 0)
{
obj* x_423; obj* x_426; obj* x_428; obj* x_429; 
lean::dec(x_23);
lean::dec(x_92);
x_423 = lean::cnstr_get(x_418, 1);
lean::inc(x_423);
lean::dec(x_418);
x_426 = lean::cnstr_get(x_419, 0);
if (lean::is_exclusive(x_419)) {
 x_428 = x_419;
} else {
 lean::inc(x_426);
 lean::dec(x_419);
 x_428 = lean::box(0);
}
if (lean::is_scalar(x_428)) {
 x_429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_429 = x_428;
}
lean::cnstr_set(x_429, 0, x_426);
x_3 = x_429;
x_4 = x_423;
goto lbl_5;
}
else
{
obj* x_430; obj* x_431; obj* x_434; obj* x_435; obj* x_436; obj* x_437; 
if (lean::is_exclusive(x_419)) {
 lean::cnstr_release(x_419, 0);
 x_430 = x_419;
} else {
 lean::dec(x_419);
 x_430 = lean::box(0);
}
x_431 = lean::cnstr_get(x_418, 1);
lean::inc(x_431);
lean::dec(x_418);
x_434 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_434, 0, x_92);
lean::cnstr_set(x_434, 1, x_23);
x_435 = l_list_reverse___rarg(x_434);
x_436 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_436, 0, x_435);
if (lean::is_scalar(x_430)) {
 x_437 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_437 = x_430;
}
lean::cnstr_set(x_437, 0, x_436);
x_3 = x_437;
x_4 = x_431;
goto lbl_5;
}
}
}
else
{
obj* x_438; 
x_438 = lean::box(0);
x_393 = x_438;
goto lbl_394;
}
lbl_394:
{
obj* x_440; obj* x_442; obj* x_443; 
lean::dec(x_393);
x_440 = l_list_reverse___rarg(x_390);
lean::inc(x_0);
x_442 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(x_0, x_440, x_387);
x_443 = lean::cnstr_get(x_442, 0);
lean::inc(x_443);
if (lean::obj_tag(x_443) == 0)
{
obj* x_447; obj* x_450; obj* x_452; obj* x_453; 
lean::dec(x_23);
lean::dec(x_92);
x_447 = lean::cnstr_get(x_442, 1);
lean::inc(x_447);
lean::dec(x_442);
x_450 = lean::cnstr_get(x_443, 0);
if (lean::is_exclusive(x_443)) {
 x_452 = x_443;
} else {
 lean::inc(x_450);
 lean::dec(x_443);
 x_452 = lean::box(0);
}
if (lean::is_scalar(x_452)) {
 x_453 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_453 = x_452;
}
lean::cnstr_set(x_453, 0, x_450);
x_3 = x_453;
x_4 = x_447;
goto lbl_5;
}
else
{
obj* x_454; obj* x_455; obj* x_458; obj* x_459; obj* x_460; obj* x_461; 
if (lean::is_exclusive(x_443)) {
 lean::cnstr_release(x_443, 0);
 x_454 = x_443;
} else {
 lean::dec(x_443);
 x_454 = lean::box(0);
}
x_455 = lean::cnstr_get(x_442, 1);
lean::inc(x_455);
lean::dec(x_442);
x_458 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_458, 0, x_92);
lean::cnstr_set(x_458, 1, x_23);
x_459 = l_list_reverse___rarg(x_458);
x_460 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_460, 0, x_459);
if (lean::is_scalar(x_454)) {
 x_461 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_461 = x_454;
}
lean::cnstr_set(x_461, 0, x_460);
x_3 = x_461;
x_4 = x_455;
goto lbl_5;
}
}
}
else
{
obj* x_463; obj* x_465; obj* x_466; obj* x_468; obj* x_471; obj* x_473; obj* x_475; obj* x_476; 
lean::dec(x_374);
x_463 = lean::cnstr_get(x_380, 1);
if (lean::is_exclusive(x_380)) {
 lean::cnstr_release(x_380, 0);
 lean::cnstr_set(x_380, 1, lean::box(0));
 x_465 = x_380;
} else {
 lean::inc(x_463);
 lean::dec(x_380);
 x_465 = lean::box(0);
}
x_466 = lean::cnstr_get(x_382, 0);
lean::inc(x_466);
x_468 = lean::cnstr_get(x_382, 1);
lean::inc(x_468);
lean::dec(x_382);
x_471 = lean::cnstr_get(x_466, 5);
lean::inc(x_471);
x_473 = l_list_reverse___rarg(x_471);
lean::inc(x_0);
x_475 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_473, x_463);
x_476 = lean::cnstr_get(x_475, 0);
lean::inc(x_476);
if (lean::obj_tag(x_476) == 0)
{
obj* x_486; obj* x_489; obj* x_491; obj* x_492; 
lean::dec(x_466);
lean::dec(x_465);
lean::dec(x_468);
lean::dec(x_23);
lean::dec(x_92);
lean::dec(x_91);
lean::dec(x_94);
lean::dec(x_373);
x_486 = lean::cnstr_get(x_475, 1);
lean::inc(x_486);
lean::dec(x_475);
x_489 = lean::cnstr_get(x_476, 0);
if (lean::is_exclusive(x_476)) {
 x_491 = x_476;
} else {
 lean::inc(x_489);
 lean::dec(x_476);
 x_491 = lean::box(0);
}
if (lean::is_scalar(x_491)) {
 x_492 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_492 = x_491;
}
lean::cnstr_set(x_492, 0, x_489);
x_3 = x_492;
x_4 = x_486;
goto lbl_5;
}
else
{
obj* x_493; obj* x_494; obj* x_496; obj* x_497; obj* x_499; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; obj* x_508; 
if (lean::is_exclusive(x_476)) {
 lean::cnstr_release(x_476, 0);
 x_493 = x_476;
} else {
 lean::dec(x_476);
 x_493 = lean::box(0);
}
x_494 = lean::cnstr_get(x_475, 1);
if (lean::is_exclusive(x_475)) {
 lean::cnstr_release(x_475, 0);
 x_496 = x_475;
} else {
 lean::inc(x_494);
 lean::dec(x_475);
 x_496 = lean::box(0);
}
x_497 = lean::cnstr_get(x_466, 6);
lean::inc(x_497);
x_499 = lean::cnstr_get(x_466, 7);
lean::inc(x_499);
lean::dec(x_466);
x_502 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_502, 0, x_92);
lean::cnstr_set(x_502, 1, x_23);
if (lean::is_scalar(x_496)) {
 x_503 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_503 = x_496;
}
lean::cnstr_set(x_503, 0, x_499);
lean::cnstr_set(x_503, 1, x_502);
if (lean::is_scalar(x_465)) {
 x_504 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_504 = x_465;
}
lean::cnstr_set(x_504, 0, x_497);
lean::cnstr_set(x_504, 1, x_503);
if (lean::is_scalar(x_373)) {
 x_505 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_505 = x_373;
}
lean::cnstr_set(x_505, 0, x_468);
lean::cnstr_set(x_505, 1, x_504);
if (lean::is_scalar(x_91)) {
 x_506 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_506 = x_91;
}
lean::cnstr_set(x_506, 0, x_94);
lean::cnstr_set(x_506, 1, x_505);
x_507 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_507, 0, x_506);
if (lean::is_scalar(x_493)) {
 x_508 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_508 = x_493;
}
lean::cnstr_set(x_508, 0, x_507);
x_3 = x_508;
x_4 = x_494;
goto lbl_5;
}
}
}
}
}
}
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_module_parser(x_0, x_2, x_3);
return x_4;
}
}
obj* _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::inc(x_1);
x_6 = l_lean_file__map_from__string(x_1);
lean::inc(x_1);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_1);
lean::cnstr_set(x_8, 2, x_6);
x_9 = l_lean_expander_builtin__transformers;
lean::inc(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1;
lean::inc(x_4);
x_14 = l_lean_parser_run___at_lean_run__frontend___spec__1(x_4, x_1, x_12);
lean::inc(x_4);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_4);
x_17 = l_lean_elaborator_run(x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_21);
x_23 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14(x_2, x_22, x_3);
return x_23;
}
}
obj* l_lean_run__frontend(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; 
lean::inc(x_1);
lean::inc(x_0);
x_9 = l_lean_mk__config(x_0, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_12 = x_9;
} else {
 lean::inc(x_10);
 lean::dec(x_9);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
lean::inc(x_3);
x_4 = x_13;
x_5 = x_3;
goto lbl_6;
}
else
{
obj* x_15; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_17 = x_9;
} else {
 lean::inc(x_15);
 lean::dec(x_9);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
lean::inc(x_3);
x_4 = x_18;
x_5 = x_3;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_25 = x_4;
} else {
 lean::inc(x_23);
 lean::dec(x_4);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_5);
return x_27;
}
else
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_4, 0);
lean::inc(x_28);
lean::dec(x_4);
x_31 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(x_0, x_1, x_2, x_5, x_28);
return x_31;
}
}
}
}
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_run__frontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_run__frontend(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
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
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = lean::box(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
lean::inc(x_0);
x_7 = l_lean_run__frontend(x_0, x_1, x_5, x_3);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_17; 
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
lean::dec(x_7);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
if (x_2 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; uint8 x_31; obj* x_32; obj* x_33; 
x_19 = lean::box(0);
x_20 = l_lean_elaborator_notation_elaborate___closed__1;
x_21 = 2;
x_22 = l_string_join___closed__1;
x_23 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_19);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set(x_23, 4, x_14);
lean::cnstr_set_scalar(x_23, sizeof(void*)*5, x_21);
x_24 = x_23;
x_25 = l_lean_message_to__string(x_24);
x_26 = l_io_println___at_lean_run__frontend___spec__3(x_25, x_11);
lean::dec(x_25);
x_28 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_30 = x_26;
} else {
 lean::inc(x_28);
 lean::dec(x_26);
 x_30 = lean::box(0);
}
x_31 = 0;
x_32 = lean::box(x_31);
if (lean::is_scalar(x_30)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_30;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_28);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_0);
x_35 = lean::box(0);
x_17 = x_35;
goto lbl_18;
}
lbl_18:
{
obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; 
lean::dec(x_17);
x_37 = l_string_quote(x_14);
x_38 = l_lean_process__file___closed__1;
x_39 = lean::string_append(x_38, x_37);
lean::dec(x_37);
x_41 = l_lean_process__file___lambda__1___closed__7;
x_42 = lean::string_append(x_39, x_41);
x_43 = l_io_println___at_lean_run__frontend___spec__3(x_42, x_11);
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
x_48 = 0;
x_49 = lean::box(x_48);
if (lean::is_scalar(x_47)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_47;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_45);
return x_50;
}
}
else
{
obj* x_53; obj* x_55; uint8 x_56; obj* x_57; obj* x_58; 
lean::dec(x_9);
lean::dec(x_0);
x_53 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_55 = x_7;
} else {
 lean::inc(x_53);
 lean::dec(x_7);
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
 l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1 = _init_l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1();
lean::mark_persistent(l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1);
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5);
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1();
lean::mark_persistent(l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1);
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

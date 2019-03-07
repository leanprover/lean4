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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*);
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
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed(obj*, obj*);
obj* l_lean_elaborator_run(obj*);
extern obj* l_lean_message__log_empty;
extern obj* l_lean_format_be___main___closed__1;
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___boxed(obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14(obj*, uint8, obj*, obj*);
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6;
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_io_println___at_lean_run__frontend___spec__3(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(obj*, obj*, obj*, uint8, obj*, obj*);
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
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
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborator died!!");
return x_0;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
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
x_27 = lean::box(0);
lean::inc(x_19);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_29, 0, x_13);
lean::closure_set(x_29, 1, x_19);
if (lean::obj_tag(x_24) == 0)
{
obj* x_32; 
x_32 = l_lean_elaborator_notation_elaborate___closed__1;
x_30 = x_32;
goto lbl_31;
}
else
{
obj* x_33; obj* x_35; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_33, 3);
lean::inc(x_35);
lean::dec(x_33);
x_30 = x_35;
goto lbl_31;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_0);
x_39 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_41 = x_4;
} else {
 lean::inc(x_39);
 lean::dec(x_4);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_5);
return x_43;
}
else
{
obj* x_44; obj* x_46; 
x_44 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_46 = x_4;
} else {
 lean::inc(x_44);
 lean::dec(x_4);
 x_46 = lean::box(0);
}
if (lean::obj_tag(x_44) == 0)
{
obj* x_48; 
lean::dec(x_46);
x_48 = lean::cnstr_get(x_44, 0);
lean::inc(x_48);
lean::dec(x_44);
x_2 = x_48;
x_3 = x_5;
goto _start;
}
else
{
obj* x_53; obj* x_56; obj* x_57; 
lean::dec(x_0);
x_53 = lean::cnstr_get(x_44, 0);
lean::inc(x_53);
lean::dec(x_44);
if (lean::is_scalar(x_46)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_46;
}
lean::cnstr_set(x_56, 0, x_53);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_5);
return x_57;
}
}
}
lbl_31:
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1;
x_59 = l_lean_profileit__pure___rarg(x_58, x_30, x_29, x_3);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_69; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_26);
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_60);
lean::dec(x_30);
x_69 = lean::cnstr_get(x_59, 1);
lean::inc(x_69);
lean::dec(x_59);
x_72 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2;
x_73 = l_io_println___at_lean_run__frontend___spec__3(x_72, x_69);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_77; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_24);
x_77 = lean::cnstr_get(x_73, 1);
lean::inc(x_77);
lean::dec(x_73);
x_80 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_82 = x_74;
} else {
 lean::inc(x_80);
 lean::dec(x_74);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
x_4 = x_83;
x_5 = x_77;
goto lbl_6;
}
else
{
obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; 
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_84 = x_74;
} else {
 lean::dec(x_74);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_73, 1);
lean::inc(x_85);
lean::dec(x_73);
x_88 = l_list_reverse___rarg(x_24);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
if (lean::is_scalar(x_84)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_84;
}
lean::cnstr_set(x_90, 0, x_89);
x_4 = x_90;
x_5 = x_85;
goto lbl_6;
}
}
else
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_99; obj* x_101; obj* x_103; 
x_91 = lean::cnstr_get(x_59, 1);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_set(x_59, 1, lean::box(0));
 x_93 = x_59;
} else {
 lean::inc(x_91);
 lean::dec(x_59);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_60, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_60, 1);
lean::inc(x_96);
lean::dec(x_60);
x_101 = lean::cnstr_get(x_94, 1);
lean::inc(x_101);
x_103 = l_list_reverse___rarg(x_101);
if (lean::obj_tag(x_103) == 0)
{
obj* x_105; 
lean::dec(x_21);
x_105 = lean::box(0);
x_99 = x_105;
goto lbl_100;
}
else
{
obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_26);
lean::dec(x_93);
lean::inc(x_103);
lean::inc(x_0);
x_110 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_103, x_91);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 lean::cnstr_release(x_103, 1);
 x_111 = x_103;
} else {
 lean::dec(x_103);
 x_111 = lean::box(0);
}
x_112 = lean::cnstr_get(x_110, 0);
lean::inc(x_112);
if (lean::obj_tag(x_112) == 0)
{
obj* x_123; obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_96);
lean::dec(x_30);
lean::dec(x_111);
x_123 = lean::cnstr_get(x_110, 1);
lean::inc(x_123);
lean::dec(x_110);
x_126 = lean::cnstr_get(x_112, 0);
if (lean::is_exclusive(x_112)) {
 x_128 = x_112;
} else {
 lean::inc(x_126);
 lean::dec(x_112);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
x_4 = x_129;
x_5 = x_123;
goto lbl_6;
}
else
{
obj* x_131; obj* x_133; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_112);
x_131 = lean::cnstr_get(x_110, 1);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_set(x_110, 1, lean::box(0));
 x_133 = x_110;
} else {
 lean::inc(x_131);
 lean::dec(x_110);
 x_133 = lean::box(0);
}
lean::inc(x_22);
lean::inc(x_94);
x_136 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1___boxed), 3, 2);
lean::closure_set(x_136, 0, x_94);
lean::closure_set(x_136, 1, x_22);
x_137 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3;
x_138 = l_lean_profileit__pure___rarg(x_137, x_30, x_136, x_131);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
lean::dec(x_30);
if (x_1 == 0)
{
obj* x_145; obj* x_147; obj* x_148; obj* x_152; obj* x_153; 
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_111);
x_145 = lean::cnstr_get(x_138, 1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_set(x_138, 1, lean::box(0));
 x_147 = x_138;
} else {
 lean::inc(x_145);
 lean::dec(x_138);
 x_147 = lean::box(0);
}
x_148 = lean::cnstr_get(x_139, 0);
lean::inc(x_148);
lean::dec(x_139);
lean::inc(x_0);
x_152 = lean::apply_2(x_0, x_148, x_145);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
if (lean::obj_tag(x_153) == 0)
{
obj* x_162; obj* x_165; obj* x_167; obj* x_168; 
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_96);
lean::dec(x_133);
lean::dec(x_147);
x_162 = lean::cnstr_get(x_152, 1);
lean::inc(x_162);
lean::dec(x_152);
x_165 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 x_167 = x_153;
} else {
 lean::inc(x_165);
 lean::dec(x_153);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_165);
x_4 = x_168;
x_5 = x_162;
goto lbl_6;
}
else
{
obj* x_169; obj* x_170; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_169 = x_153;
} else {
 lean::dec(x_153);
 x_169 = lean::box(0);
}
x_170 = lean::cnstr_get(x_152, 1);
if (lean::is_exclusive(x_152)) {
 lean::cnstr_release(x_152, 0);
 x_172 = x_152;
} else {
 lean::inc(x_170);
 lean::dec(x_152);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_22);
lean::cnstr_set(x_173, 1, x_27);
if (lean::is_scalar(x_147)) {
 x_174 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_174 = x_147;
}
lean::cnstr_set(x_174, 0, x_19);
lean::cnstr_set(x_174, 1, x_173);
if (lean::is_scalar(x_133)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_133;
}
lean::cnstr_set(x_175, 0, x_16);
lean::cnstr_set(x_175, 1, x_174);
if (lean::is_scalar(x_21)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_21;
}
lean::cnstr_set(x_176, 0, x_96);
lean::cnstr_set(x_176, 1, x_175);
x_177 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_177, 0, x_176);
if (lean::is_scalar(x_169)) {
 x_178 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_178 = x_169;
}
lean::cnstr_set(x_178, 0, x_177);
x_4 = x_178;
x_5 = x_170;
goto lbl_6;
}
}
else
{
obj* x_179; obj* x_181; obj* x_182; obj* x_186; obj* x_187; 
x_179 = lean::cnstr_get(x_138, 1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_set(x_138, 1, lean::box(0));
 x_181 = x_138;
} else {
 lean::inc(x_179);
 lean::dec(x_138);
 x_181 = lean::box(0);
}
x_182 = lean::cnstr_get(x_139, 0);
lean::inc(x_182);
lean::dec(x_139);
lean::inc(x_0);
x_186 = lean::apply_2(x_0, x_182, x_179);
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_199; obj* x_202; obj* x_204; obj* x_205; 
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_96);
lean::dec(x_181);
lean::dec(x_133);
lean::dec(x_111);
x_199 = lean::cnstr_get(x_186, 1);
lean::inc(x_199);
lean::dec(x_186);
x_202 = lean::cnstr_get(x_187, 0);
if (lean::is_exclusive(x_187)) {
 x_204 = x_187;
} else {
 lean::inc(x_202);
 lean::dec(x_187);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_202);
x_4 = x_205;
x_5 = x_199;
goto lbl_6;
}
else
{
obj* x_206; obj* x_207; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 x_206 = x_187;
} else {
 lean::dec(x_187);
 x_206 = lean::box(0);
}
x_207 = lean::cnstr_get(x_186, 1);
if (lean::is_exclusive(x_186)) {
 lean::cnstr_release(x_186, 0);
 x_209 = x_186;
} else {
 lean::inc(x_207);
 lean::dec(x_186);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_210 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_210 = x_111;
}
lean::cnstr_set(x_210, 0, x_94);
lean::cnstr_set(x_210, 1, x_24);
if (lean::is_scalar(x_209)) {
 x_211 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_211 = x_209;
}
lean::cnstr_set(x_211, 0, x_22);
lean::cnstr_set(x_211, 1, x_210);
if (lean::is_scalar(x_181)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_181;
}
lean::cnstr_set(x_212, 0, x_19);
lean::cnstr_set(x_212, 1, x_211);
if (lean::is_scalar(x_133)) {
 x_213 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_213 = x_133;
}
lean::cnstr_set(x_213, 0, x_16);
lean::cnstr_set(x_213, 1, x_212);
if (lean::is_scalar(x_21)) {
 x_214 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_214 = x_21;
}
lean::cnstr_set(x_214, 0, x_96);
lean::cnstr_set(x_214, 1, x_213);
x_215 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_215, 0, x_214);
if (lean::is_scalar(x_206)) {
 x_216 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_216 = x_206;
}
lean::cnstr_set(x_216, 0, x_215);
x_4 = x_216;
x_5 = x_207;
goto lbl_6;
}
}
}
else
{
obj* x_220; obj* x_222; obj* x_223; obj* x_227; obj* x_228; obj* x_229; obj* x_231; 
lean::dec(x_21);
lean::dec(x_19);
lean::dec(x_22);
x_220 = lean::cnstr_get(x_138, 1);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_set(x_138, 1, lean::box(0));
 x_222 = x_138;
} else {
 lean::inc(x_220);
 lean::dec(x_138);
 x_222 = lean::box(0);
}
x_223 = lean::cnstr_get(x_139, 0);
lean::inc(x_223);
lean::dec(x_139);
lean::inc(x_223);
x_227 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_227, 0, x_16);
lean::closure_set(x_227, 1, x_223);
x_228 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4;
x_229 = l_lean_profileit__pure___rarg(x_228, x_30, x_227, x_220);
lean::dec(x_30);
x_231 = lean::cnstr_get(x_229, 0);
lean::inc(x_231);
if (lean::obj_tag(x_231) == 0)
{
obj* x_236; obj* x_239; obj* x_242; obj* x_244; uint8 x_245; 
lean::dec(x_222);
lean::dec(x_96);
lean::dec(x_133);
x_236 = lean::cnstr_get(x_229, 1);
lean::inc(x_236);
lean::dec(x_229);
x_239 = lean::cnstr_get(x_231, 0);
lean::inc(x_239);
lean::dec(x_231);
x_244 = l_lean_parser_module_eoi;
x_245 = l_lean_parser_syntax_is__of__kind___main(x_244, x_223);
lean::dec(x_223);
if (x_245 == 0)
{
obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_111);
x_248 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6;
x_249 = l_io_println___at_lean_run__frontend___spec__3(x_248, x_236);
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
obj* x_255; obj* x_258; obj* x_260; obj* x_261; 
lean::dec(x_239);
lean::dec(x_24);
lean::dec(x_94);
x_255 = lean::cnstr_get(x_249, 1);
lean::inc(x_255);
lean::dec(x_249);
x_258 = lean::cnstr_get(x_250, 0);
if (lean::is_exclusive(x_250)) {
 x_260 = x_250;
} else {
 lean::inc(x_258);
 lean::dec(x_250);
 x_260 = lean::box(0);
}
if (lean::is_scalar(x_260)) {
 x_261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_261 = x_260;
}
lean::cnstr_set(x_261, 0, x_258);
x_4 = x_261;
x_5 = x_255;
goto lbl_6;
}
else
{
obj* x_263; obj* x_266; obj* x_268; obj* x_269; 
lean::dec(x_250);
x_263 = lean::cnstr_get(x_249, 1);
lean::inc(x_263);
lean::dec(x_249);
x_266 = l_list_reverse___rarg(x_239);
lean::inc(x_0);
x_268 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_266, x_263);
x_269 = lean::cnstr_get(x_268, 0);
lean::inc(x_269);
if (lean::obj_tag(x_269) == 0)
{
obj* x_273; obj* x_276; obj* x_278; obj* x_279; 
lean::dec(x_24);
lean::dec(x_94);
x_273 = lean::cnstr_get(x_268, 1);
lean::inc(x_273);
lean::dec(x_268);
x_276 = lean::cnstr_get(x_269, 0);
if (lean::is_exclusive(x_269)) {
 x_278 = x_269;
} else {
 lean::inc(x_276);
 lean::dec(x_269);
 x_278 = lean::box(0);
}
if (lean::is_scalar(x_278)) {
 x_279 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_279 = x_278;
}
lean::cnstr_set(x_279, 0, x_276);
x_4 = x_279;
x_5 = x_273;
goto lbl_6;
}
else
{
obj* x_280; 
if (lean::is_exclusive(x_269)) {
 lean::cnstr_release(x_269, 0);
 x_280 = x_269;
} else {
 lean::dec(x_269);
 x_280 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_284; obj* x_287; 
lean::dec(x_280);
lean::dec(x_24);
lean::dec(x_94);
x_284 = lean::cnstr_get(x_268, 1);
lean::inc(x_284);
lean::dec(x_268);
x_287 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
x_4 = x_287;
x_5 = x_284;
goto lbl_6;
}
else
{
obj* x_288; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
x_288 = lean::cnstr_get(x_268, 1);
lean::inc(x_288);
lean::dec(x_268);
x_291 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_291, 0, x_94);
lean::cnstr_set(x_291, 1, x_24);
x_292 = l_list_reverse___rarg(x_291);
x_293 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_293, 0, x_292);
if (lean::is_scalar(x_280)) {
 x_294 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_294 = x_280;
}
lean::cnstr_set(x_294, 0, x_293);
x_4 = x_294;
x_5 = x_288;
goto lbl_6;
}
}
}
}
else
{
obj* x_295; 
x_295 = lean::box(0);
x_242 = x_295;
goto lbl_243;
}
lbl_243:
{
obj* x_297; obj* x_299; obj* x_300; 
lean::dec(x_242);
x_297 = l_list_reverse___rarg(x_239);
lean::inc(x_0);
x_299 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_297, x_236);
x_300 = lean::cnstr_get(x_299, 0);
lean::inc(x_300);
if (lean::obj_tag(x_300) == 0)
{
obj* x_305; obj* x_308; obj* x_310; obj* x_311; 
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_111);
x_305 = lean::cnstr_get(x_299, 1);
lean::inc(x_305);
lean::dec(x_299);
x_308 = lean::cnstr_get(x_300, 0);
if (lean::is_exclusive(x_300)) {
 x_310 = x_300;
} else {
 lean::inc(x_308);
 lean::dec(x_300);
 x_310 = lean::box(0);
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_308);
x_4 = x_311;
x_5 = x_305;
goto lbl_6;
}
else
{
obj* x_312; 
if (lean::is_exclusive(x_300)) {
 lean::cnstr_release(x_300, 0);
 x_312 = x_300;
} else {
 lean::dec(x_300);
 x_312 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_317; obj* x_320; 
lean::dec(x_312);
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_111);
x_317 = lean::cnstr_get(x_299, 1);
lean::inc(x_317);
lean::dec(x_299);
x_320 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
x_4 = x_320;
x_5 = x_317;
goto lbl_6;
}
else
{
obj* x_321; obj* x_324; obj* x_325; obj* x_326; obj* x_327; 
x_321 = lean::cnstr_get(x_299, 1);
lean::inc(x_321);
lean::dec(x_299);
if (lean::is_scalar(x_111)) {
 x_324 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_324 = x_111;
}
lean::cnstr_set(x_324, 0, x_94);
lean::cnstr_set(x_324, 1, x_24);
x_325 = l_list_reverse___rarg(x_324);
x_326 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_326, 0, x_325);
if (lean::is_scalar(x_312)) {
 x_327 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_327 = x_312;
}
lean::cnstr_set(x_327, 0, x_326);
x_4 = x_327;
x_5 = x_321;
goto lbl_6;
}
}
}
}
else
{
obj* x_329; obj* x_331; obj* x_332; obj* x_334; obj* x_337; obj* x_339; obj* x_341; obj* x_342; 
lean::dec(x_223);
x_329 = lean::cnstr_get(x_229, 1);
if (lean::is_exclusive(x_229)) {
 lean::cnstr_release(x_229, 0);
 lean::cnstr_set(x_229, 1, lean::box(0));
 x_331 = x_229;
} else {
 lean::inc(x_329);
 lean::dec(x_229);
 x_331 = lean::box(0);
}
x_332 = lean::cnstr_get(x_231, 0);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_231, 1);
lean::inc(x_334);
lean::dec(x_231);
x_337 = lean::cnstr_get(x_332, 5);
lean::inc(x_337);
x_339 = l_list_reverse___rarg(x_337);
lean::inc(x_0);
x_341 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_339, x_329);
x_342 = lean::cnstr_get(x_341, 0);
lean::inc(x_342);
if (lean::obj_tag(x_342) == 0)
{
obj* x_353; obj* x_356; obj* x_358; obj* x_359; 
lean::dec(x_222);
lean::dec(x_24);
lean::dec(x_334);
lean::dec(x_94);
lean::dec(x_96);
lean::dec(x_332);
lean::dec(x_331);
lean::dec(x_133);
lean::dec(x_111);
x_353 = lean::cnstr_get(x_341, 1);
lean::inc(x_353);
lean::dec(x_341);
x_356 = lean::cnstr_get(x_342, 0);
if (lean::is_exclusive(x_342)) {
 x_358 = x_342;
} else {
 lean::inc(x_356);
 lean::dec(x_342);
 x_358 = lean::box(0);
}
if (lean::is_scalar(x_358)) {
 x_359 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_359 = x_358;
}
lean::cnstr_set(x_359, 0, x_356);
x_4 = x_359;
x_5 = x_353;
goto lbl_6;
}
else
{
obj* x_360; 
if (lean::is_exclusive(x_342)) {
 lean::cnstr_release(x_342, 0);
 x_360 = x_342;
} else {
 lean::dec(x_342);
 x_360 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_364; obj* x_366; obj* x_367; obj* x_369; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; 
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_111);
x_364 = lean::cnstr_get(x_341, 1);
if (lean::is_exclusive(x_341)) {
 lean::cnstr_release(x_341, 0);
 x_366 = x_341;
} else {
 lean::inc(x_364);
 lean::dec(x_341);
 x_366 = lean::box(0);
}
x_367 = lean::cnstr_get(x_332, 6);
lean::inc(x_367);
x_369 = lean::cnstr_get(x_332, 7);
lean::inc(x_369);
lean::dec(x_332);
if (lean::is_scalar(x_366)) {
 x_372 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_372 = x_366;
}
lean::cnstr_set(x_372, 0, x_369);
lean::cnstr_set(x_372, 1, x_27);
if (lean::is_scalar(x_331)) {
 x_373 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_373 = x_331;
}
lean::cnstr_set(x_373, 0, x_367);
lean::cnstr_set(x_373, 1, x_372);
if (lean::is_scalar(x_222)) {
 x_374 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_374 = x_222;
}
lean::cnstr_set(x_374, 0, x_334);
lean::cnstr_set(x_374, 1, x_373);
if (lean::is_scalar(x_133)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_133;
}
lean::cnstr_set(x_375, 0, x_96);
lean::cnstr_set(x_375, 1, x_374);
x_376 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_376, 0, x_375);
if (lean::is_scalar(x_360)) {
 x_377 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_377 = x_360;
}
lean::cnstr_set(x_377, 0, x_376);
x_4 = x_377;
x_5 = x_364;
goto lbl_6;
}
else
{
obj* x_378; obj* x_380; obj* x_381; obj* x_383; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
x_378 = lean::cnstr_get(x_341, 1);
if (lean::is_exclusive(x_341)) {
 lean::cnstr_release(x_341, 0);
 x_380 = x_341;
} else {
 lean::inc(x_378);
 lean::dec(x_341);
 x_380 = lean::box(0);
}
x_381 = lean::cnstr_get(x_332, 6);
lean::inc(x_381);
x_383 = lean::cnstr_get(x_332, 7);
lean::inc(x_383);
lean::dec(x_332);
if (lean::is_scalar(x_111)) {
 x_386 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_386 = x_111;
}
lean::cnstr_set(x_386, 0, x_94);
lean::cnstr_set(x_386, 1, x_24);
if (lean::is_scalar(x_380)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_380;
}
lean::cnstr_set(x_387, 0, x_383);
lean::cnstr_set(x_387, 1, x_386);
if (lean::is_scalar(x_331)) {
 x_388 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_388 = x_331;
}
lean::cnstr_set(x_388, 0, x_381);
lean::cnstr_set(x_388, 1, x_387);
if (lean::is_scalar(x_222)) {
 x_389 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_389 = x_222;
}
lean::cnstr_set(x_389, 0, x_334);
lean::cnstr_set(x_389, 1, x_388);
if (lean::is_scalar(x_133)) {
 x_390 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_390 = x_133;
}
lean::cnstr_set(x_390, 0, x_96);
lean::cnstr_set(x_390, 1, x_389);
x_391 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_391, 0, x_390);
if (lean::is_scalar(x_360)) {
 x_392 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_392 = x_360;
}
lean::cnstr_set(x_392, 0, x_391);
x_4 = x_392;
x_5 = x_378;
goto lbl_6;
}
}
}
}
}
}
lbl_100:
{
obj* x_396; obj* x_397; obj* x_398; obj* x_399; 
lean::dec(x_99);
lean::inc(x_22);
lean::inc(x_94);
x_396 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___lambda__1___boxed), 3, 2);
lean::closure_set(x_396, 0, x_94);
lean::closure_set(x_396, 1, x_22);
x_397 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__3;
x_398 = l_lean_profileit__pure___rarg(x_397, x_30, x_396, x_91);
x_399 = lean::cnstr_get(x_398, 0);
lean::inc(x_399);
if (lean::obj_tag(x_399) == 0)
{
lean::dec(x_30);
if (x_1 == 0)
{
obj* x_404; obj* x_406; obj* x_407; obj* x_411; obj* x_412; 
lean::dec(x_24);
lean::dec(x_94);
x_404 = lean::cnstr_get(x_398, 1);
if (lean::is_exclusive(x_398)) {
 lean::cnstr_release(x_398, 0);
 lean::cnstr_set(x_398, 1, lean::box(0));
 x_406 = x_398;
} else {
 lean::inc(x_404);
 lean::dec(x_398);
 x_406 = lean::box(0);
}
x_407 = lean::cnstr_get(x_399, 0);
lean::inc(x_407);
lean::dec(x_399);
lean::inc(x_0);
x_411 = lean::apply_2(x_0, x_407, x_404);
x_412 = lean::cnstr_get(x_411, 0);
lean::inc(x_412);
if (lean::obj_tag(x_412) == 0)
{
obj* x_421; obj* x_424; obj* x_426; obj* x_427; 
lean::dec(x_26);
lean::dec(x_16);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_96);
lean::dec(x_93);
lean::dec(x_406);
x_421 = lean::cnstr_get(x_411, 1);
lean::inc(x_421);
lean::dec(x_411);
x_424 = lean::cnstr_get(x_412, 0);
if (lean::is_exclusive(x_412)) {
 x_426 = x_412;
} else {
 lean::inc(x_424);
 lean::dec(x_412);
 x_426 = lean::box(0);
}
if (lean::is_scalar(x_426)) {
 x_427 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_427 = x_426;
}
lean::cnstr_set(x_427, 0, x_424);
x_4 = x_427;
x_5 = x_421;
goto lbl_6;
}
else
{
obj* x_428; obj* x_429; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_436; obj* x_437; 
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 x_428 = x_412;
} else {
 lean::dec(x_412);
 x_428 = lean::box(0);
}
x_429 = lean::cnstr_get(x_411, 1);
if (lean::is_exclusive(x_411)) {
 lean::cnstr_release(x_411, 0);
 x_431 = x_411;
} else {
 lean::inc(x_429);
 lean::dec(x_411);
 x_431 = lean::box(0);
}
if (lean::is_scalar(x_431)) {
 x_432 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_432 = x_431;
}
lean::cnstr_set(x_432, 0, x_22);
lean::cnstr_set(x_432, 1, x_27);
if (lean::is_scalar(x_406)) {
 x_433 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_433 = x_406;
}
lean::cnstr_set(x_433, 0, x_19);
lean::cnstr_set(x_433, 1, x_432);
if (lean::is_scalar(x_93)) {
 x_434 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_434 = x_93;
}
lean::cnstr_set(x_434, 0, x_16);
lean::cnstr_set(x_434, 1, x_433);
if (lean::is_scalar(x_26)) {
 x_435 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_435 = x_26;
}
lean::cnstr_set(x_435, 0, x_96);
lean::cnstr_set(x_435, 1, x_434);
x_436 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_436, 0, x_435);
if (lean::is_scalar(x_428)) {
 x_437 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_437 = x_428;
}
lean::cnstr_set(x_437, 0, x_436);
x_4 = x_437;
x_5 = x_429;
goto lbl_6;
}
}
else
{
obj* x_438; obj* x_440; obj* x_441; obj* x_445; obj* x_446; 
x_438 = lean::cnstr_get(x_398, 1);
if (lean::is_exclusive(x_398)) {
 lean::cnstr_release(x_398, 0);
 lean::cnstr_set(x_398, 1, lean::box(0));
 x_440 = x_398;
} else {
 lean::inc(x_438);
 lean::dec(x_398);
 x_440 = lean::box(0);
}
x_441 = lean::cnstr_get(x_399, 0);
lean::inc(x_441);
lean::dec(x_399);
lean::inc(x_0);
x_445 = lean::apply_2(x_0, x_441, x_438);
x_446 = lean::cnstr_get(x_445, 0);
lean::inc(x_446);
if (lean::obj_tag(x_446) == 0)
{
obj* x_457; obj* x_460; obj* x_462; obj* x_463; 
lean::dec(x_26);
lean::dec(x_16);
lean::dec(x_19);
lean::dec(x_22);
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_96);
lean::dec(x_93);
lean::dec(x_440);
x_457 = lean::cnstr_get(x_445, 1);
lean::inc(x_457);
lean::dec(x_445);
x_460 = lean::cnstr_get(x_446, 0);
if (lean::is_exclusive(x_446)) {
 x_462 = x_446;
} else {
 lean::inc(x_460);
 lean::dec(x_446);
 x_462 = lean::box(0);
}
if (lean::is_scalar(x_462)) {
 x_463 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_463 = x_462;
}
lean::cnstr_set(x_463, 0, x_460);
x_4 = x_463;
x_5 = x_457;
goto lbl_6;
}
else
{
obj* x_464; obj* x_465; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; 
if (lean::is_exclusive(x_446)) {
 lean::cnstr_release(x_446, 0);
 x_464 = x_446;
} else {
 lean::dec(x_446);
 x_464 = lean::box(0);
}
x_465 = lean::cnstr_get(x_445, 1);
if (lean::is_exclusive(x_445)) {
 lean::cnstr_release(x_445, 0);
 x_467 = x_445;
} else {
 lean::inc(x_465);
 lean::dec(x_445);
 x_467 = lean::box(0);
}
x_468 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_468, 0, x_94);
lean::cnstr_set(x_468, 1, x_24);
if (lean::is_scalar(x_467)) {
 x_469 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_469 = x_467;
}
lean::cnstr_set(x_469, 0, x_22);
lean::cnstr_set(x_469, 1, x_468);
if (lean::is_scalar(x_440)) {
 x_470 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_470 = x_440;
}
lean::cnstr_set(x_470, 0, x_19);
lean::cnstr_set(x_470, 1, x_469);
if (lean::is_scalar(x_93)) {
 x_471 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_471 = x_93;
}
lean::cnstr_set(x_471, 0, x_16);
lean::cnstr_set(x_471, 1, x_470);
if (lean::is_scalar(x_26)) {
 x_472 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_472 = x_26;
}
lean::cnstr_set(x_472, 0, x_96);
lean::cnstr_set(x_472, 1, x_471);
x_473 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_473, 0, x_472);
if (lean::is_scalar(x_464)) {
 x_474 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_474 = x_464;
}
lean::cnstr_set(x_474, 0, x_473);
x_4 = x_474;
x_5 = x_465;
goto lbl_6;
}
}
}
else
{
obj* x_478; obj* x_480; obj* x_481; obj* x_485; obj* x_486; obj* x_487; obj* x_489; 
lean::dec(x_26);
lean::dec(x_19);
lean::dec(x_22);
x_478 = lean::cnstr_get(x_398, 1);
if (lean::is_exclusive(x_398)) {
 lean::cnstr_release(x_398, 0);
 lean::cnstr_set(x_398, 1, lean::box(0));
 x_480 = x_398;
} else {
 lean::inc(x_478);
 lean::dec(x_398);
 x_480 = lean::box(0);
}
x_481 = lean::cnstr_get(x_399, 0);
lean::inc(x_481);
lean::dec(x_399);
lean::inc(x_481);
x_485 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad___rarg___lambda__9___boxed), 3, 2);
lean::closure_set(x_485, 0, x_16);
lean::closure_set(x_485, 1, x_481);
x_486 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__4;
x_487 = l_lean_profileit__pure___rarg(x_486, x_30, x_485, x_478);
lean::dec(x_30);
x_489 = lean::cnstr_get(x_487, 0);
lean::inc(x_489);
if (lean::obj_tag(x_489) == 0)
{
obj* x_494; obj* x_497; obj* x_500; obj* x_502; uint8 x_503; 
lean::dec(x_480);
lean::dec(x_96);
lean::dec(x_93);
x_494 = lean::cnstr_get(x_487, 1);
lean::inc(x_494);
lean::dec(x_487);
x_497 = lean::cnstr_get(x_489, 0);
lean::inc(x_497);
lean::dec(x_489);
x_502 = l_lean_parser_module_eoi;
x_503 = l_lean_parser_syntax_is__of__kind___main(x_502, x_481);
lean::dec(x_481);
if (x_503 == 0)
{
obj* x_505; obj* x_506; obj* x_507; 
x_505 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6;
x_506 = l_io_println___at_lean_run__frontend___spec__3(x_505, x_494);
x_507 = lean::cnstr_get(x_506, 0);
lean::inc(x_507);
if (lean::obj_tag(x_507) == 0)
{
obj* x_512; obj* x_515; obj* x_517; obj* x_518; 
lean::dec(x_24);
lean::dec(x_497);
lean::dec(x_94);
x_512 = lean::cnstr_get(x_506, 1);
lean::inc(x_512);
lean::dec(x_506);
x_515 = lean::cnstr_get(x_507, 0);
if (lean::is_exclusive(x_507)) {
 x_517 = x_507;
} else {
 lean::inc(x_515);
 lean::dec(x_507);
 x_517 = lean::box(0);
}
if (lean::is_scalar(x_517)) {
 x_518 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_518 = x_517;
}
lean::cnstr_set(x_518, 0, x_515);
x_4 = x_518;
x_5 = x_512;
goto lbl_6;
}
else
{
obj* x_520; obj* x_523; obj* x_525; obj* x_526; 
lean::dec(x_507);
x_520 = lean::cnstr_get(x_506, 1);
lean::inc(x_520);
lean::dec(x_506);
x_523 = l_list_reverse___rarg(x_497);
lean::inc(x_0);
x_525 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_523, x_520);
x_526 = lean::cnstr_get(x_525, 0);
lean::inc(x_526);
if (lean::obj_tag(x_526) == 0)
{
obj* x_530; obj* x_533; obj* x_535; obj* x_536; 
lean::dec(x_24);
lean::dec(x_94);
x_530 = lean::cnstr_get(x_525, 1);
lean::inc(x_530);
lean::dec(x_525);
x_533 = lean::cnstr_get(x_526, 0);
if (lean::is_exclusive(x_526)) {
 x_535 = x_526;
} else {
 lean::inc(x_533);
 lean::dec(x_526);
 x_535 = lean::box(0);
}
if (lean::is_scalar(x_535)) {
 x_536 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_536 = x_535;
}
lean::cnstr_set(x_536, 0, x_533);
x_4 = x_536;
x_5 = x_530;
goto lbl_6;
}
else
{
obj* x_537; 
if (lean::is_exclusive(x_526)) {
 lean::cnstr_release(x_526, 0);
 x_537 = x_526;
} else {
 lean::dec(x_526);
 x_537 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_541; obj* x_544; 
lean::dec(x_24);
lean::dec(x_537);
lean::dec(x_94);
x_541 = lean::cnstr_get(x_525, 1);
lean::inc(x_541);
lean::dec(x_525);
x_544 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
x_4 = x_544;
x_5 = x_541;
goto lbl_6;
}
else
{
obj* x_545; obj* x_548; obj* x_549; obj* x_550; obj* x_551; 
x_545 = lean::cnstr_get(x_525, 1);
lean::inc(x_545);
lean::dec(x_525);
x_548 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_548, 0, x_94);
lean::cnstr_set(x_548, 1, x_24);
x_549 = l_list_reverse___rarg(x_548);
x_550 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_550, 0, x_549);
if (lean::is_scalar(x_537)) {
 x_551 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_551 = x_537;
}
lean::cnstr_set(x_551, 0, x_550);
x_4 = x_551;
x_5 = x_545;
goto lbl_6;
}
}
}
}
else
{
obj* x_552; 
x_552 = lean::box(0);
x_500 = x_552;
goto lbl_501;
}
lbl_501:
{
obj* x_554; obj* x_556; obj* x_557; 
lean::dec(x_500);
x_554 = l_list_reverse___rarg(x_497);
lean::inc(x_0);
x_556 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(x_0, x_554, x_494);
x_557 = lean::cnstr_get(x_556, 0);
lean::inc(x_557);
if (lean::obj_tag(x_557) == 0)
{
obj* x_561; obj* x_564; obj* x_566; obj* x_567; 
lean::dec(x_24);
lean::dec(x_94);
x_561 = lean::cnstr_get(x_556, 1);
lean::inc(x_561);
lean::dec(x_556);
x_564 = lean::cnstr_get(x_557, 0);
if (lean::is_exclusive(x_557)) {
 x_566 = x_557;
} else {
 lean::inc(x_564);
 lean::dec(x_557);
 x_566 = lean::box(0);
}
if (lean::is_scalar(x_566)) {
 x_567 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_567 = x_566;
}
lean::cnstr_set(x_567, 0, x_564);
x_4 = x_567;
x_5 = x_561;
goto lbl_6;
}
else
{
obj* x_568; 
if (lean::is_exclusive(x_557)) {
 lean::cnstr_release(x_557, 0);
 x_568 = x_557;
} else {
 lean::dec(x_557);
 x_568 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_572; obj* x_575; 
lean::dec(x_568);
lean::dec(x_24);
lean::dec(x_94);
x_572 = lean::cnstr_get(x_556, 1);
lean::inc(x_572);
lean::dec(x_556);
x_575 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__5;
x_4 = x_575;
x_5 = x_572;
goto lbl_6;
}
else
{
obj* x_576; obj* x_579; obj* x_580; obj* x_581; obj* x_582; 
x_576 = lean::cnstr_get(x_556, 1);
lean::inc(x_576);
lean::dec(x_556);
x_579 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_579, 0, x_94);
lean::cnstr_set(x_579, 1, x_24);
x_580 = l_list_reverse___rarg(x_579);
x_581 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_581, 0, x_580);
if (lean::is_scalar(x_568)) {
 x_582 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_582 = x_568;
}
lean::cnstr_set(x_582, 0, x_581);
x_4 = x_582;
x_5 = x_576;
goto lbl_6;
}
}
}
}
else
{
obj* x_584; obj* x_586; obj* x_587; obj* x_589; obj* x_592; obj* x_594; obj* x_596; obj* x_597; 
lean::dec(x_481);
x_584 = lean::cnstr_get(x_487, 1);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_release(x_487, 0);
 lean::cnstr_set(x_487, 1, lean::box(0));
 x_586 = x_487;
} else {
 lean::inc(x_584);
 lean::dec(x_487);
 x_586 = lean::box(0);
}
x_587 = lean::cnstr_get(x_489, 0);
lean::inc(x_587);
x_589 = lean::cnstr_get(x_489, 1);
lean::inc(x_589);
lean::dec(x_489);
x_592 = lean::cnstr_get(x_587, 5);
lean::inc(x_592);
x_594 = l_list_reverse___rarg(x_592);
lean::inc(x_0);
x_596 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_594, x_584);
x_597 = lean::cnstr_get(x_596, 0);
lean::inc(x_597);
if (lean::obj_tag(x_597) == 0)
{
obj* x_607; obj* x_610; obj* x_612; obj* x_613; 
lean::dec(x_480);
lean::dec(x_24);
lean::dec(x_94);
lean::dec(x_96);
lean::dec(x_93);
lean::dec(x_587);
lean::dec(x_586);
lean::dec(x_589);
x_607 = lean::cnstr_get(x_596, 1);
lean::inc(x_607);
lean::dec(x_596);
x_610 = lean::cnstr_get(x_597, 0);
if (lean::is_exclusive(x_597)) {
 x_612 = x_597;
} else {
 lean::inc(x_610);
 lean::dec(x_597);
 x_612 = lean::box(0);
}
if (lean::is_scalar(x_612)) {
 x_613 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_613 = x_612;
}
lean::cnstr_set(x_613, 0, x_610);
x_4 = x_613;
x_5 = x_607;
goto lbl_6;
}
else
{
obj* x_614; 
if (lean::is_exclusive(x_597)) {
 lean::cnstr_release(x_597, 0);
 x_614 = x_597;
} else {
 lean::dec(x_597);
 x_614 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_617; obj* x_619; obj* x_620; obj* x_622; obj* x_625; obj* x_626; obj* x_627; obj* x_628; obj* x_629; obj* x_630; 
lean::dec(x_24);
lean::dec(x_94);
x_617 = lean::cnstr_get(x_596, 1);
if (lean::is_exclusive(x_596)) {
 lean::cnstr_release(x_596, 0);
 x_619 = x_596;
} else {
 lean::inc(x_617);
 lean::dec(x_596);
 x_619 = lean::box(0);
}
x_620 = lean::cnstr_get(x_587, 6);
lean::inc(x_620);
x_622 = lean::cnstr_get(x_587, 7);
lean::inc(x_622);
lean::dec(x_587);
if (lean::is_scalar(x_619)) {
 x_625 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_625 = x_619;
}
lean::cnstr_set(x_625, 0, x_622);
lean::cnstr_set(x_625, 1, x_27);
if (lean::is_scalar(x_586)) {
 x_626 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_626 = x_586;
}
lean::cnstr_set(x_626, 0, x_620);
lean::cnstr_set(x_626, 1, x_625);
if (lean::is_scalar(x_480)) {
 x_627 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_627 = x_480;
}
lean::cnstr_set(x_627, 0, x_589);
lean::cnstr_set(x_627, 1, x_626);
if (lean::is_scalar(x_93)) {
 x_628 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_628 = x_93;
}
lean::cnstr_set(x_628, 0, x_96);
lean::cnstr_set(x_628, 1, x_627);
x_629 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_629, 0, x_628);
if (lean::is_scalar(x_614)) {
 x_630 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_630 = x_614;
}
lean::cnstr_set(x_630, 0, x_629);
x_4 = x_630;
x_5 = x_617;
goto lbl_6;
}
else
{
obj* x_631; obj* x_633; obj* x_634; obj* x_636; obj* x_639; obj* x_640; obj* x_641; obj* x_642; obj* x_643; obj* x_644; obj* x_645; 
x_631 = lean::cnstr_get(x_596, 1);
if (lean::is_exclusive(x_596)) {
 lean::cnstr_release(x_596, 0);
 x_633 = x_596;
} else {
 lean::inc(x_631);
 lean::dec(x_596);
 x_633 = lean::box(0);
}
x_634 = lean::cnstr_get(x_587, 6);
lean::inc(x_634);
x_636 = lean::cnstr_get(x_587, 7);
lean::inc(x_636);
lean::dec(x_587);
x_639 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_639, 0, x_94);
lean::cnstr_set(x_639, 1, x_24);
if (lean::is_scalar(x_633)) {
 x_640 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_640 = x_633;
}
lean::cnstr_set(x_640, 0, x_636);
lean::cnstr_set(x_640, 1, x_639);
if (lean::is_scalar(x_586)) {
 x_641 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_641 = x_586;
}
lean::cnstr_set(x_641, 0, x_634);
lean::cnstr_set(x_641, 1, x_640);
if (lean::is_scalar(x_480)) {
 x_642 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_642 = x_480;
}
lean::cnstr_set(x_642, 0, x_589);
lean::cnstr_set(x_642, 1, x_641);
if (lean::is_scalar(x_93)) {
 x_643 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_643 = x_93;
}
lean::cnstr_set(x_643, 0, x_96);
lean::cnstr_set(x_643, 1, x_642);
x_644 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_644, 0, x_643);
if (lean::is_scalar(x_614)) {
 x_645 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_645 = x_614;
}
lean::cnstr_set(x_645, 0, x_644);
x_4 = x_645;
x_5 = x_631;
goto lbl_6;
}
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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::inc(x_1);
x_7 = l_lean_file__map_from__string(x_1);
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_7);
x_10 = l_lean_expander_builtin__transformers;
lean::inc(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1;
lean::inc(x_5);
x_15 = l_lean_parser_run___at_lean_run__frontend___spec__1(x_5, x_1, x_13);
lean::inc(x_5);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_5);
x_18 = l_lean_elaborator_run(x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_5);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14(x_2, x_3, x_23, x_4);
return x_24;
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
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_5, 0);
lean::inc(x_29);
lean::dec(x_5);
x_32 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(x_0, x_1, x_2, x_3, x_6, x_29);
return x_32;
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
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14(x_0, x_4, x_2, x_3);
return x_5;
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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
x_7 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(x_0, x_1, x_2, x_6, x_4, x_5);
return x_7;
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
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__6);
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

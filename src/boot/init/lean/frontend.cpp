// Lean compiler output
// Module: init.lean.frontend
// Imports: init.default init.lean.parser.module init.lean.expander init.lean.elaborator init.io
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
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
extern obj* l_lean_parser_module_tokens;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__6;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_string_quote(obj*);
obj* l_coroutine_resume___rarg(obj*, obj*);
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_run__expander(obj*, obj*);
obj* l_lean_mk__config(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_lean_process__file___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_io_prim_put__str___boxed(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_lean_run__elaborator___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj*, obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_lean_elaborator_run(obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_run__parser(obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_reader__t_run___rarg(obj*, obj*);
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_io_prim_lift__eio___at_lean_run__frontend___spec__6(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(obj*, obj*, obj*);
extern obj* l_lean_parser_run___rarg___closed__1;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l_lean_file__map_from__string(obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2(obj*, obj*);
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
obj* l_lean_run__expander___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_io_print___at_lean_run__frontend___spec__4(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___lambda__1(obj*, obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_io_println___at_lean_run__frontend___spec__3(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_lean_run__elaborator(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1(obj*);
obj* l_lean_run__parser___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__4;
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
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
obj* l_lean_run__parser___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_lean_run__parser(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__parser___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_run__expander___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_lean_run__expander(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__expander___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_run__elaborator___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* l_lean_run__elaborator(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__elaborator___rarg), 2, 0);
return x_4;
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
obj* x_3; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_15);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_2);
x_5 = lean::string_mk_iterator(x_1);
x_6 = lean::apply_2(x_0, x_5, x_3);
x_7 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 3);
lean::inc(x_8);
x_10 = l_option_get___main___at_lean_parser_run___spec__2(x_8);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_15, 0);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_lean_parser_message__of__parsec__message___rarg(x_18, x_5);
x_22 = l_lean_message__log_empty;
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_27; obj* x_30; obj* x_32; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_0);
x_27 = lean::cnstr_get(x_2, 0);
lean::inc(x_27);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
x_35 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_35, 0, x_30);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_37, 0, x_36);
return x_37;
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
obj* l_io_prim_lift__eio___at_lean_run__frontend___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
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
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
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
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
}
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_put__str___boxed), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_lean_run__frontend___spec__6(x_2, x_1);
return x_3;
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
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
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
x_12 = lean::alloc_cnstr(0, 2, 0);
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
obj* _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parser died!!");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborator died!!");
return x_0;
}
}
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_23; obj* x_26; obj* x_28; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
lean::dec(x_18);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_26, 0, x_6);
lean::inc(x_16);
x_28 = l_lean_run__parser___rarg(x_26, x_16);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_11);
lean::dec(x_28);
x_33 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
x_34 = l_io_println___at_lean_run__frontend___spec__3(x_33, x_2);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_38; obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_23);
x_38 = lean::cnstr_get(x_34, 1);
lean::inc(x_38);
lean::dec(x_34);
x_41 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_43 = x_35;
} else {
 lean::inc(x_41);
 lean::dec(x_35);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
x_3 = x_44;
x_4 = x_38;
goto lbl_5;
}
else
{
obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_45 = x_35;
} else {
 lean::dec(x_35);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_34, 1);
lean::inc(x_46);
lean::dec(x_34);
x_49 = l_list_reverse___rarg(x_23);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
if (lean::is_scalar(x_45)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_45;
}
lean::cnstr_set(x_51, 0, x_50);
x_3 = x_51;
x_4 = x_46;
goto lbl_5;
}
}
else
{
obj* x_52; obj* x_54; obj* x_57; obj* x_59; 
x_52 = lean::cnstr_get(x_28, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_28, 1);
lean::inc(x_54);
lean::dec(x_28);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
x_59 = l_list_reverse___rarg(x_57);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_62; obj* x_63; obj* x_65; 
x_60 = lean::cnstr_get(x_52, 0);
lean::inc(x_60);
x_62 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_62, 0, x_60);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_63, 0, x_62);
lean::inc(x_21);
x_65 = l_lean_run__expander___rarg(x_63, x_21);
if (lean::obj_tag(x_65) == 0)
{
obj* x_66; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
lean::dec(x_65);
lean::inc(x_0);
x_70 = lean::apply_2(x_0, x_66, x_2);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_79; obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_23);
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_11);
lean::dec(x_52);
lean::dec(x_54);
x_79 = lean::cnstr_get(x_70, 1);
lean::inc(x_79);
lean::dec(x_70);
x_82 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_84 = x_71;
} else {
 lean::inc(x_82);
 lean::dec(x_71);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
x_3 = x_85;
x_4 = x_79;
goto lbl_5;
}
else
{
obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_86 = x_71;
} else {
 lean::dec(x_71);
 x_86 = lean::box(0);
}
x_87 = lean::cnstr_get(x_70, 1);
lean::inc(x_87);
lean::dec(x_70);
x_90 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_90, 0, x_52);
lean::cnstr_set(x_90, 1, x_23);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_21);
lean::cnstr_set(x_91, 1, x_90);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_16);
lean::cnstr_set(x_92, 1, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_11);
lean::cnstr_set(x_93, 1, x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_54);
lean::cnstr_set(x_94, 1, x_93);
x_95 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
if (lean::is_scalar(x_86)) {
 x_96 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_96 = x_86;
}
lean::cnstr_set(x_96, 0, x_95);
x_3 = x_96;
x_4 = x_87;
goto lbl_5;
}
}
else
{
obj* x_99; obj* x_102; obj* x_104; 
lean::dec(x_16);
lean::dec(x_21);
x_99 = lean::cnstr_get(x_65, 0);
lean::inc(x_99);
lean::dec(x_65);
x_102 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_102, 0, x_11);
lean::inc(x_99);
x_104 = l_lean_run__elaborator___rarg(x_102, x_99);
if (lean::obj_tag(x_104) == 0)
{
obj* x_106; obj* x_109; uint8 x_110; 
lean::dec(x_54);
x_106 = lean::cnstr_get(x_104, 0);
lean::inc(x_106);
lean::dec(x_104);
x_109 = l_lean_parser_module_eoi;
x_110 = l_lean_parser_syntax_is__of__kind___main(x_109, x_99);
if (x_110 == 0)
{
obj* x_111; obj* x_112; obj* x_113; 
x_111 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
x_112 = l_io_println___at_lean_run__frontend___spec__3(x_111, x_2);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
if (lean::obj_tag(x_113) == 0)
{
obj* x_118; obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_23);
lean::dec(x_52);
lean::dec(x_106);
x_118 = lean::cnstr_get(x_112, 1);
lean::inc(x_118);
lean::dec(x_112);
x_121 = lean::cnstr_get(x_113, 0);
if (lean::is_exclusive(x_113)) {
 x_123 = x_113;
} else {
 lean::inc(x_121);
 lean::dec(x_113);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_121);
x_3 = x_124;
x_4 = x_118;
goto lbl_5;
}
else
{
obj* x_126; obj* x_129; obj* x_131; obj* x_132; 
lean::dec(x_113);
x_126 = lean::cnstr_get(x_112, 1);
lean::inc(x_126);
lean::dec(x_112);
x_129 = l_list_reverse___rarg(x_106);
lean::inc(x_0);
x_131 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_129, x_126);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
if (lean::obj_tag(x_132) == 0)
{
obj* x_136; obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_23);
lean::dec(x_52);
x_136 = lean::cnstr_get(x_131, 1);
lean::inc(x_136);
lean::dec(x_131);
x_139 = lean::cnstr_get(x_132, 0);
if (lean::is_exclusive(x_132)) {
 x_141 = x_132;
} else {
 lean::inc(x_139);
 lean::dec(x_132);
 x_141 = lean::box(0);
}
if (lean::is_scalar(x_141)) {
 x_142 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_142 = x_141;
}
lean::cnstr_set(x_142, 0, x_139);
x_3 = x_142;
x_4 = x_136;
goto lbl_5;
}
else
{
obj* x_143; obj* x_144; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 x_143 = x_132;
} else {
 lean::dec(x_132);
 x_143 = lean::box(0);
}
x_144 = lean::cnstr_get(x_131, 1);
lean::inc(x_144);
lean::dec(x_131);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_52);
lean::cnstr_set(x_147, 1, x_23);
x_148 = l_list_reverse___rarg(x_147);
x_149 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_149, 0, x_148);
if (lean::is_scalar(x_143)) {
 x_150 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_150 = x_143;
}
lean::cnstr_set(x_150, 0, x_149);
x_3 = x_150;
x_4 = x_144;
goto lbl_5;
}
}
}
else
{
obj* x_151; obj* x_153; obj* x_154; 
x_151 = l_list_reverse___rarg(x_106);
lean::inc(x_0);
x_153 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_151, x_2);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
if (lean::obj_tag(x_154) == 0)
{
obj* x_158; obj* x_161; obj* x_163; obj* x_164; 
lean::dec(x_23);
lean::dec(x_52);
x_158 = lean::cnstr_get(x_153, 1);
lean::inc(x_158);
lean::dec(x_153);
x_161 = lean::cnstr_get(x_154, 0);
if (lean::is_exclusive(x_154)) {
 x_163 = x_154;
} else {
 lean::inc(x_161);
 lean::dec(x_154);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
x_3 = x_164;
x_4 = x_158;
goto lbl_5;
}
else
{
obj* x_165; obj* x_166; obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_165 = x_154;
} else {
 lean::dec(x_154);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_153, 1);
lean::inc(x_166);
lean::dec(x_153);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_52);
lean::cnstr_set(x_169, 1, x_23);
x_170 = l_list_reverse___rarg(x_169);
x_171 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_171, 0, x_170);
if (lean::is_scalar(x_165)) {
 x_172 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_172 = x_165;
}
lean::cnstr_set(x_172, 0, x_171);
x_3 = x_172;
x_4 = x_166;
goto lbl_5;
}
}
}
else
{
obj* x_174; obj* x_176; obj* x_179; obj* x_181; obj* x_183; obj* x_184; 
lean::dec(x_99);
x_174 = lean::cnstr_get(x_104, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_104, 1);
lean::inc(x_176);
lean::dec(x_104);
x_179 = lean::cnstr_get(x_174, 5);
lean::inc(x_179);
x_181 = l_list_reverse___rarg(x_179);
lean::inc(x_0);
x_183 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_181, x_2);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
if (lean::obj_tag(x_184) == 0)
{
obj* x_191; obj* x_194; obj* x_196; obj* x_197; 
lean::dec(x_174);
lean::dec(x_176);
lean::dec(x_23);
lean::dec(x_52);
lean::dec(x_54);
x_191 = lean::cnstr_get(x_183, 1);
lean::inc(x_191);
lean::dec(x_183);
x_194 = lean::cnstr_get(x_184, 0);
if (lean::is_exclusive(x_184)) {
 x_196 = x_184;
} else {
 lean::inc(x_194);
 lean::dec(x_184);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_194);
x_3 = x_197;
x_4 = x_191;
goto lbl_5;
}
else
{
obj* x_198; obj* x_199; obj* x_202; obj* x_204; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_198 = x_184;
} else {
 lean::dec(x_184);
 x_198 = lean::box(0);
}
x_199 = lean::cnstr_get(x_183, 1);
lean::inc(x_199);
lean::dec(x_183);
x_202 = lean::cnstr_get(x_174, 6);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_174, 7);
lean::inc(x_204);
lean::dec(x_174);
x_207 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_207, 0, x_52);
lean::cnstr_set(x_207, 1, x_23);
x_208 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_208, 0, x_204);
lean::cnstr_set(x_208, 1, x_207);
x_209 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_209, 0, x_202);
lean::cnstr_set(x_209, 1, x_208);
x_210 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_210, 0, x_176);
lean::cnstr_set(x_210, 1, x_209);
x_211 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_211, 0, x_54);
lean::cnstr_set(x_211, 1, x_210);
x_212 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_212, 0, x_211);
if (lean::is_scalar(x_198)) {
 x_213 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_213 = x_198;
}
lean::cnstr_set(x_213, 0, x_212);
x_3 = x_213;
x_4 = x_199;
goto lbl_5;
}
}
}
}
else
{
obj* x_216; obj* x_217; obj* x_218; 
lean::inc(x_59);
lean::inc(x_0);
x_216 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_59, x_2);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 lean::cnstr_release(x_59, 1);
 x_217 = x_59;
} else {
 lean::dec(x_59);
 x_217 = lean::box(0);
}
x_218 = lean::cnstr_get(x_216, 0);
lean::inc(x_218);
if (lean::obj_tag(x_218) == 0)
{
obj* x_227; obj* x_230; obj* x_232; obj* x_233; 
lean::dec(x_23);
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_11);
lean::dec(x_217);
lean::dec(x_52);
lean::dec(x_54);
x_227 = lean::cnstr_get(x_216, 1);
lean::inc(x_227);
lean::dec(x_216);
x_230 = lean::cnstr_get(x_218, 0);
if (lean::is_exclusive(x_218)) {
 x_232 = x_218;
} else {
 lean::inc(x_230);
 lean::dec(x_218);
 x_232 = lean::box(0);
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_230);
x_3 = x_233;
x_4 = x_227;
goto lbl_5;
}
else
{
obj* x_235; obj* x_238; obj* x_240; obj* x_241; obj* x_243; 
lean::dec(x_218);
x_235 = lean::cnstr_get(x_216, 1);
lean::inc(x_235);
lean::dec(x_216);
x_238 = lean::cnstr_get(x_52, 0);
lean::inc(x_238);
x_240 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_240, 0, x_238);
x_241 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_241, 0, x_240);
lean::inc(x_21);
x_243 = l_lean_run__expander___rarg(x_241, x_21);
if (lean::obj_tag(x_243) == 0)
{
obj* x_244; obj* x_248; obj* x_249; 
x_244 = lean::cnstr_get(x_243, 0);
lean::inc(x_244);
lean::dec(x_243);
lean::inc(x_0);
x_248 = lean::apply_2(x_0, x_244, x_235);
x_249 = lean::cnstr_get(x_248, 0);
lean::inc(x_249);
if (lean::obj_tag(x_249) == 0)
{
obj* x_258; obj* x_261; obj* x_263; obj* x_264; 
lean::dec(x_23);
lean::dec(x_16);
lean::dec(x_21);
lean::dec(x_11);
lean::dec(x_217);
lean::dec(x_52);
lean::dec(x_54);
x_258 = lean::cnstr_get(x_248, 1);
lean::inc(x_258);
lean::dec(x_248);
x_261 = lean::cnstr_get(x_249, 0);
if (lean::is_exclusive(x_249)) {
 x_263 = x_249;
} else {
 lean::inc(x_261);
 lean::dec(x_249);
 x_263 = lean::box(0);
}
if (lean::is_scalar(x_263)) {
 x_264 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_264 = x_263;
}
lean::cnstr_set(x_264, 0, x_261);
x_3 = x_264;
x_4 = x_258;
goto lbl_5;
}
else
{
obj* x_265; obj* x_266; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 0);
 x_265 = x_249;
} else {
 lean::dec(x_249);
 x_265 = lean::box(0);
}
x_266 = lean::cnstr_get(x_248, 1);
lean::inc(x_266);
lean::dec(x_248);
if (lean::is_scalar(x_217)) {
 x_269 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_269 = x_217;
}
lean::cnstr_set(x_269, 0, x_52);
lean::cnstr_set(x_269, 1, x_23);
x_270 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_270, 0, x_21);
lean::cnstr_set(x_270, 1, x_269);
x_271 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_271, 0, x_16);
lean::cnstr_set(x_271, 1, x_270);
x_272 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_272, 0, x_11);
lean::cnstr_set(x_272, 1, x_271);
x_273 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_273, 0, x_54);
lean::cnstr_set(x_273, 1, x_272);
x_274 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
if (lean::is_scalar(x_265)) {
 x_275 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_275 = x_265;
}
lean::cnstr_set(x_275, 0, x_274);
x_3 = x_275;
x_4 = x_266;
goto lbl_5;
}
}
else
{
obj* x_278; obj* x_281; obj* x_283; 
lean::dec(x_16);
lean::dec(x_21);
x_278 = lean::cnstr_get(x_243, 0);
lean::inc(x_278);
lean::dec(x_243);
x_281 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_281, 0, x_11);
lean::inc(x_278);
x_283 = l_lean_run__elaborator___rarg(x_281, x_278);
if (lean::obj_tag(x_283) == 0)
{
obj* x_285; obj* x_288; uint8 x_289; 
lean::dec(x_54);
x_285 = lean::cnstr_get(x_283, 0);
lean::inc(x_285);
lean::dec(x_283);
x_288 = l_lean_parser_module_eoi;
x_289 = l_lean_parser_syntax_is__of__kind___main(x_288, x_278);
if (x_289 == 0)
{
obj* x_290; obj* x_291; obj* x_292; 
x_290 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
x_291 = l_io_println___at_lean_run__frontend___spec__3(x_290, x_235);
x_292 = lean::cnstr_get(x_291, 0);
lean::inc(x_292);
if (lean::obj_tag(x_292) == 0)
{
obj* x_298; obj* x_301; obj* x_303; obj* x_304; 
lean::dec(x_23);
lean::dec(x_217);
lean::dec(x_52);
lean::dec(x_285);
x_298 = lean::cnstr_get(x_291, 1);
lean::inc(x_298);
lean::dec(x_291);
x_301 = lean::cnstr_get(x_292, 0);
if (lean::is_exclusive(x_292)) {
 x_303 = x_292;
} else {
 lean::inc(x_301);
 lean::dec(x_292);
 x_303 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_304 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_304 = x_303;
}
lean::cnstr_set(x_304, 0, x_301);
x_3 = x_304;
x_4 = x_298;
goto lbl_5;
}
else
{
obj* x_306; obj* x_309; obj* x_311; obj* x_312; 
lean::dec(x_292);
x_306 = lean::cnstr_get(x_291, 1);
lean::inc(x_306);
lean::dec(x_291);
x_309 = l_list_reverse___rarg(x_285);
lean::inc(x_0);
x_311 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_309, x_306);
x_312 = lean::cnstr_get(x_311, 0);
lean::inc(x_312);
if (lean::obj_tag(x_312) == 0)
{
obj* x_317; obj* x_320; obj* x_322; obj* x_323; 
lean::dec(x_23);
lean::dec(x_217);
lean::dec(x_52);
x_317 = lean::cnstr_get(x_311, 1);
lean::inc(x_317);
lean::dec(x_311);
x_320 = lean::cnstr_get(x_312, 0);
if (lean::is_exclusive(x_312)) {
 x_322 = x_312;
} else {
 lean::inc(x_320);
 lean::dec(x_312);
 x_322 = lean::box(0);
}
if (lean::is_scalar(x_322)) {
 x_323 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_323 = x_322;
}
lean::cnstr_set(x_323, 0, x_320);
x_3 = x_323;
x_4 = x_317;
goto lbl_5;
}
else
{
obj* x_324; obj* x_325; obj* x_328; obj* x_329; obj* x_330; obj* x_331; 
if (lean::is_exclusive(x_312)) {
 lean::cnstr_release(x_312, 0);
 x_324 = x_312;
} else {
 lean::dec(x_312);
 x_324 = lean::box(0);
}
x_325 = lean::cnstr_get(x_311, 1);
lean::inc(x_325);
lean::dec(x_311);
if (lean::is_scalar(x_217)) {
 x_328 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_328 = x_217;
}
lean::cnstr_set(x_328, 0, x_52);
lean::cnstr_set(x_328, 1, x_23);
x_329 = l_list_reverse___rarg(x_328);
x_330 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_330, 0, x_329);
if (lean::is_scalar(x_324)) {
 x_331 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_331 = x_324;
}
lean::cnstr_set(x_331, 0, x_330);
x_3 = x_331;
x_4 = x_325;
goto lbl_5;
}
}
}
else
{
obj* x_332; obj* x_334; obj* x_335; 
x_332 = l_list_reverse___rarg(x_285);
lean::inc(x_0);
x_334 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_332, x_235);
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
if (lean::obj_tag(x_335) == 0)
{
obj* x_340; obj* x_343; obj* x_345; obj* x_346; 
lean::dec(x_23);
lean::dec(x_217);
lean::dec(x_52);
x_340 = lean::cnstr_get(x_334, 1);
lean::inc(x_340);
lean::dec(x_334);
x_343 = lean::cnstr_get(x_335, 0);
if (lean::is_exclusive(x_335)) {
 x_345 = x_335;
} else {
 lean::inc(x_343);
 lean::dec(x_335);
 x_345 = lean::box(0);
}
if (lean::is_scalar(x_345)) {
 x_346 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_346 = x_345;
}
lean::cnstr_set(x_346, 0, x_343);
x_3 = x_346;
x_4 = x_340;
goto lbl_5;
}
else
{
obj* x_347; obj* x_348; obj* x_351; obj* x_352; obj* x_353; obj* x_354; 
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 x_347 = x_335;
} else {
 lean::dec(x_335);
 x_347 = lean::box(0);
}
x_348 = lean::cnstr_get(x_334, 1);
lean::inc(x_348);
lean::dec(x_334);
if (lean::is_scalar(x_217)) {
 x_351 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_351 = x_217;
}
lean::cnstr_set(x_351, 0, x_52);
lean::cnstr_set(x_351, 1, x_23);
x_352 = l_list_reverse___rarg(x_351);
x_353 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_353, 0, x_352);
if (lean::is_scalar(x_347)) {
 x_354 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_354 = x_347;
}
lean::cnstr_set(x_354, 0, x_353);
x_3 = x_354;
x_4 = x_348;
goto lbl_5;
}
}
}
else
{
obj* x_356; obj* x_358; obj* x_361; obj* x_363; obj* x_365; obj* x_366; 
lean::dec(x_278);
x_356 = lean::cnstr_get(x_283, 0);
lean::inc(x_356);
x_358 = lean::cnstr_get(x_283, 1);
lean::inc(x_358);
lean::dec(x_283);
x_361 = lean::cnstr_get(x_356, 5);
lean::inc(x_361);
x_363 = l_list_reverse___rarg(x_361);
lean::inc(x_0);
x_365 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_363, x_235);
x_366 = lean::cnstr_get(x_365, 0);
lean::inc(x_366);
if (lean::obj_tag(x_366) == 0)
{
obj* x_374; obj* x_377; obj* x_379; obj* x_380; 
lean::dec(x_23);
lean::dec(x_217);
lean::dec(x_52);
lean::dec(x_54);
lean::dec(x_356);
lean::dec(x_358);
x_374 = lean::cnstr_get(x_365, 1);
lean::inc(x_374);
lean::dec(x_365);
x_377 = lean::cnstr_get(x_366, 0);
if (lean::is_exclusive(x_366)) {
 x_379 = x_366;
} else {
 lean::inc(x_377);
 lean::dec(x_366);
 x_379 = lean::box(0);
}
if (lean::is_scalar(x_379)) {
 x_380 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_380 = x_379;
}
lean::cnstr_set(x_380, 0, x_377);
x_3 = x_380;
x_4 = x_374;
goto lbl_5;
}
else
{
obj* x_381; obj* x_382; obj* x_385; obj* x_387; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; 
if (lean::is_exclusive(x_366)) {
 lean::cnstr_release(x_366, 0);
 x_381 = x_366;
} else {
 lean::dec(x_366);
 x_381 = lean::box(0);
}
x_382 = lean::cnstr_get(x_365, 1);
lean::inc(x_382);
lean::dec(x_365);
x_385 = lean::cnstr_get(x_356, 6);
lean::inc(x_385);
x_387 = lean::cnstr_get(x_356, 7);
lean::inc(x_387);
lean::dec(x_356);
if (lean::is_scalar(x_217)) {
 x_390 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_390 = x_217;
}
lean::cnstr_set(x_390, 0, x_52);
lean::cnstr_set(x_390, 1, x_23);
x_391 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_391, 0, x_387);
lean::cnstr_set(x_391, 1, x_390);
x_392 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_392, 0, x_385);
lean::cnstr_set(x_392, 1, x_391);
x_393 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_393, 0, x_358);
lean::cnstr_set(x_393, 1, x_392);
x_394 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_394, 0, x_54);
lean::cnstr_set(x_394, 1, x_393);
x_395 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_395, 0, x_394);
if (lean::is_scalar(x_381)) {
 x_396 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_396 = x_381;
}
lean::cnstr_set(x_396, 0, x_395);
x_3 = x_396;
x_4 = x_382;
goto lbl_5;
}
}
}
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_398; obj* x_400; obj* x_401; obj* x_402; 
lean::dec(x_0);
x_398 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_400 = x_3;
} else {
 lean::inc(x_398);
 lean::dec(x_3);
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
lean::cnstr_set(x_402, 1, x_4);
return x_402;
}
else
{
obj* x_403; obj* x_405; 
x_403 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_405 = x_3;
} else {
 lean::inc(x_403);
 lean::dec(x_3);
 x_405 = lean::box(0);
}
if (lean::obj_tag(x_403) == 0)
{
obj* x_407; 
lean::dec(x_405);
x_407 = lean::cnstr_get(x_403, 0);
lean::inc(x_407);
lean::dec(x_403);
x_1 = x_407;
x_2 = x_4;
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
lean::cnstr_set(x_416, 1, x_4);
return x_416;
}
}
}
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_lean_parser_module_parser(x_0, x_2, x_3);
return x_5;
}
}
obj* _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___lambda__1), 4, 0);
return x_0;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_12 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1;
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
x_23 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15(x_2, x_22, x_3);
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
x_4 = x_13;
x_5 = x_3;
goto lbl_6;
}
else
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
x_4 = x_17;
x_5 = x_3;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_23 = x_4;
} else {
 lean::inc(x_21);
 lean::dec(x_4);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_5);
return x_25;
}
else
{
obj* x_26; obj* x_29; 
x_26 = lean::cnstr_get(x_4, 0);
lean::inc(x_26);
lean::dec(x_4);
x_29 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__14(x_0, x_1, x_2, x_5, x_26);
return x_29;
}
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
x_6 = l_io_println___at_lean_run__frontend___spec__3(x_5, x_2);
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::box(0);
x_3 = x_7;
goto lbl_4;
}
lbl_4:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_3);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_13 = l_nat_repr(x_11);
x_14 = l_lean_process__file___lambda__1___closed__1;
x_15 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_17 = l_lean_process__file___lambda__1___closed__2;
x_18 = lean::string_append(x_15, x_17);
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::dec(x_9);
x_22 = l_nat_repr(x_19);
x_23 = lean::string_append(x_18, x_22);
lean::dec(x_22);
x_25 = l_lean_process__file___lambda__1___closed__3;
x_26 = lean::string_append(x_23, x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_28 = lean::cnstr_get(x_1, 3);
lean::inc(x_28);
x_30 = l_string_quote(x_28);
x_31 = lean::cnstr_get(x_1, 4);
lean::inc(x_31);
lean::dec(x_1);
x_34 = l_string_quote(x_31);
switch (x_27) {
case 0:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_35 = l_lean_process__file___lambda__1___closed__4;
x_36 = lean::string_append(x_26, x_35);
x_37 = l_lean_process__file___lambda__1___closed__5;
x_38 = lean::string_append(x_36, x_37);
x_39 = lean::string_append(x_38, x_30);
lean::dec(x_30);
x_41 = l_lean_process__file___lambda__1___closed__6;
x_42 = lean::string_append(x_39, x_41);
x_43 = lean::string_append(x_42, x_34);
lean::dec(x_34);
x_45 = l_lean_process__file___lambda__1___closed__7;
x_46 = lean::string_append(x_43, x_45);
x_47 = l_io_println___at_lean_run__frontend___spec__3(x_46, x_2);
return x_47;
}
case 1:
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
x_48 = l_lean_process__file___lambda__1___closed__8;
x_49 = lean::string_append(x_26, x_48);
x_50 = l_lean_process__file___lambda__1___closed__5;
x_51 = lean::string_append(x_49, x_50);
x_52 = lean::string_append(x_51, x_30);
lean::dec(x_30);
x_54 = l_lean_process__file___lambda__1___closed__6;
x_55 = lean::string_append(x_52, x_54);
x_56 = lean::string_append(x_55, x_34);
lean::dec(x_34);
x_58 = l_lean_process__file___lambda__1___closed__7;
x_59 = lean::string_append(x_56, x_58);
x_60 = l_io_println___at_lean_run__frontend___spec__3(x_59, x_2);
return x_60;
}
default:
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
x_61 = l_lean_process__file___lambda__1___closed__9;
x_62 = lean::string_append(x_26, x_61);
x_63 = l_lean_process__file___lambda__1___closed__5;
x_64 = lean::string_append(x_62, x_63);
x_65 = lean::string_append(x_64, x_30);
lean::dec(x_30);
x_67 = l_lean_process__file___lambda__1___closed__6;
x_68 = lean::string_append(x_65, x_67);
x_69 = lean::string_append(x_68, x_34);
lean::dec(x_34);
x_71 = l_lean_process__file___lambda__1___closed__7;
x_72 = lean::string_append(x_69, x_71);
x_73 = l_io_println___at_lean_run__frontend___spec__3(x_72, x_2);
return x_73;
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
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_4 = lean::box(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
lean::inc(x_0);
x_7 = l_lean_run__frontend(x_0, x_1, x_5, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
if (x_2 == 0)
{
obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_29; obj* x_30; obj* x_31; 
x_18 = lean::box(0);
x_19 = l_lean_elaborator_notation_elaborate___closed__1;
x_20 = 2;
x_21 = l_string_join___closed__1;
x_22 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set(x_22, 2, x_18);
lean::cnstr_set(x_22, 3, x_21);
lean::cnstr_set(x_22, 4, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*5, x_20);
x_23 = x_22;
x_24 = l_lean_message_to__string(x_23);
x_25 = l_io_println___at_lean_run__frontend___spec__3(x_24, x_10);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_29 = 0;
x_30 = lean::box(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_26);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_0);
x_33 = lean::box(0);
x_16 = x_33;
goto lbl_17;
}
lbl_17:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; uint8 x_45; obj* x_46; obj* x_47; 
lean::dec(x_16);
x_35 = l_string_quote(x_13);
x_36 = l_lean_process__file___closed__1;
x_37 = lean::string_append(x_36, x_35);
lean::dec(x_35);
x_39 = l_lean_process__file___lambda__1___closed__7;
x_40 = lean::string_append(x_37, x_39);
x_41 = l_io_println___at_lean_run__frontend___spec__3(x_40, x_10);
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
x_45 = 0;
x_46 = lean::box(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
return x_47;
}
}
else
{
obj* x_50; uint8 x_53; obj* x_54; obj* x_55; 
lean::dec(x_8);
lean::dec(x_0);
x_50 = lean::cnstr_get(x_7, 1);
lean::inc(x_50);
lean::dec(x_7);
x_53 = 1;
x_54 = lean::box(x_53);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
return x_55;
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
void initialize_init_io();
static bool _G_initialized = false;
void initialize_init_lean_frontend() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_default();
 initialize_init_lean_parser_module();
 initialize_init_lean_expander();
 initialize_init_lean_elaborator();
 initialize_init_io();
 l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1 = _init_l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1();
lean::mark_persistent(l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1);
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2);
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1();
lean::mark_persistent(l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1);
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

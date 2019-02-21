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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
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
if (lean::is_scalar(x_4)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_4;
}
lean::cnstr_set(x_24, 0, x_11);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_25, 0, x_24);
return x_25;
}
else
{
obj* x_28; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_4);
lean::dec(x_0);
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_28, 0);
x_33 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_35 = x_28;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_28);
 x_35 = lean::box(0);
}
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_31);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_33);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; 
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
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_release(x_6, 1);
 x_17 = x_6;
} else {
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
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
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_26, 0, x_12);
lean::inc(x_18);
x_28 = l_lean_run__parser___rarg(x_26, x_18);
if (lean::obj_tag(x_28) == 0)
{
obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_25);
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_28);
x_36 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
x_37 = l_io_println___at_lean_run__frontend___spec__3(x_36, x_2);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_23);
x_41 = lean::cnstr_get(x_37, 1);
lean::inc(x_41);
lean::dec(x_37);
x_44 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
x_3 = x_47;
x_4 = x_41;
goto lbl_5;
}
else
{
obj* x_48; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_48 = x_38;
} else {
 lean::dec(x_38);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_37, 1);
lean::inc(x_49);
lean::dec(x_37);
x_52 = l_list_reverse___rarg(x_23);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
if (lean::is_scalar(x_48)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_48;
}
lean::cnstr_set(x_54, 0, x_53);
x_3 = x_54;
x_4 = x_49;
goto lbl_5;
}
}
else
{
obj* x_55; obj* x_57; obj* x_60; obj* x_62; 
x_55 = lean::cnstr_get(x_28, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_28, 1);
lean::inc(x_57);
lean::dec(x_28);
x_60 = lean::cnstr_get(x_55, 1);
lean::inc(x_60);
x_62 = l_list_reverse___rarg(x_60);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_68; 
x_63 = lean::cnstr_get(x_55, 0);
lean::inc(x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_65, 0, x_63);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_66, 0, x_65);
lean::inc(x_21);
x_68 = l_lean_run__expander___rarg(x_66, x_21);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
lean::inc(x_0);
x_73 = lean::apply_2(x_0, x_69, x_2);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_85; obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_25);
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_57);
x_85 = lean::cnstr_get(x_73, 1);
lean::inc(x_85);
lean::dec(x_73);
x_88 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_90 = x_74;
} else {
 lean::inc(x_88);
 lean::dec(x_74);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
x_3 = x_91;
x_4 = x_85;
goto lbl_5;
}
else
{
obj* x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_92 = x_74;
} else {
 lean::dec(x_74);
 x_92 = lean::box(0);
}
x_93 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_95 = x_73;
} else {
 lean::inc(x_93);
 lean::dec(x_73);
 x_95 = lean::box(0);
}
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_55);
lean::cnstr_set(x_96, 1, x_23);
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_21);
lean::cnstr_set(x_97, 1, x_96);
if (lean::is_scalar(x_25)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_25;
}
lean::cnstr_set(x_98, 0, x_18);
lean::cnstr_set(x_98, 1, x_97);
if (lean::is_scalar(x_20)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_20;
}
lean::cnstr_set(x_99, 0, x_15);
lean::cnstr_set(x_99, 1, x_98);
if (lean::is_scalar(x_17)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_17;
}
lean::cnstr_set(x_100, 0, x_57);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
if (lean::is_scalar(x_92)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_92;
}
lean::cnstr_set(x_102, 0, x_101);
x_3 = x_102;
x_4 = x_93;
goto lbl_5;
}
}
else
{
obj* x_105; obj* x_108; obj* x_110; 
lean::dec(x_18);
lean::dec(x_21);
x_105 = lean::cnstr_get(x_68, 0);
lean::inc(x_105);
lean::dec(x_68);
x_108 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_108, 0, x_15);
lean::inc(x_105);
x_110 = l_lean_run__elaborator___rarg(x_108, x_105);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_118; uint8 x_119; 
lean::dec(x_25);
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_57);
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
lean::dec(x_110);
x_118 = l_lean_parser_module_eoi;
x_119 = l_lean_parser_syntax_is__of__kind___main(x_118, x_105);
if (x_119 == 0)
{
obj* x_120; obj* x_121; obj* x_122; 
x_120 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
x_121 = l_io_println___at_lean_run__frontend___spec__3(x_120, x_2);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
if (lean::obj_tag(x_122) == 0)
{
obj* x_127; obj* x_130; obj* x_132; obj* x_133; 
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_115);
x_127 = lean::cnstr_get(x_121, 1);
lean::inc(x_127);
lean::dec(x_121);
x_130 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_132 = x_122;
} else {
 lean::inc(x_130);
 lean::dec(x_122);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
x_3 = x_133;
x_4 = x_127;
goto lbl_5;
}
else
{
obj* x_135; obj* x_138; obj* x_140; obj* x_141; 
lean::dec(x_122);
x_135 = lean::cnstr_get(x_121, 1);
lean::inc(x_135);
lean::dec(x_121);
x_138 = l_list_reverse___rarg(x_115);
lean::inc(x_0);
x_140 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_138, x_135);
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
if (lean::obj_tag(x_141) == 0)
{
obj* x_145; obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_55);
lean::dec(x_23);
x_145 = lean::cnstr_get(x_140, 1);
lean::inc(x_145);
lean::dec(x_140);
x_148 = lean::cnstr_get(x_141, 0);
if (lean::is_exclusive(x_141)) {
 x_150 = x_141;
} else {
 lean::inc(x_148);
 lean::dec(x_141);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_3 = x_151;
x_4 = x_145;
goto lbl_5;
}
else
{
obj* x_152; obj* x_153; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
if (lean::is_exclusive(x_141)) {
 lean::cnstr_release(x_141, 0);
 x_152 = x_141;
} else {
 lean::dec(x_141);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_140, 1);
lean::inc(x_153);
lean::dec(x_140);
x_156 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_156, 0, x_55);
lean::cnstr_set(x_156, 1, x_23);
x_157 = l_list_reverse___rarg(x_156);
x_158 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_158, 0, x_157);
if (lean::is_scalar(x_152)) {
 x_159 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_159 = x_152;
}
lean::cnstr_set(x_159, 0, x_158);
x_3 = x_159;
x_4 = x_153;
goto lbl_5;
}
}
}
else
{
obj* x_160; obj* x_162; obj* x_163; 
x_160 = l_list_reverse___rarg(x_115);
lean::inc(x_0);
x_162 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_160, x_2);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
if (lean::obj_tag(x_163) == 0)
{
obj* x_167; obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_55);
lean::dec(x_23);
x_167 = lean::cnstr_get(x_162, 1);
lean::inc(x_167);
lean::dec(x_162);
x_170 = lean::cnstr_get(x_163, 0);
if (lean::is_exclusive(x_163)) {
 x_172 = x_163;
} else {
 lean::inc(x_170);
 lean::dec(x_163);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_170);
x_3 = x_173;
x_4 = x_167;
goto lbl_5;
}
else
{
obj* x_174; obj* x_175; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 x_174 = x_163;
} else {
 lean::dec(x_163);
 x_174 = lean::box(0);
}
x_175 = lean::cnstr_get(x_162, 1);
lean::inc(x_175);
lean::dec(x_162);
x_178 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_178, 0, x_55);
lean::cnstr_set(x_178, 1, x_23);
x_179 = l_list_reverse___rarg(x_178);
x_180 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_180, 0, x_179);
if (lean::is_scalar(x_174)) {
 x_181 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_181 = x_174;
}
lean::cnstr_set(x_181, 0, x_180);
x_3 = x_181;
x_4 = x_175;
goto lbl_5;
}
}
}
else
{
obj* x_183; obj* x_185; obj* x_188; obj* x_190; obj* x_192; obj* x_193; 
lean::dec(x_105);
x_183 = lean::cnstr_get(x_110, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_110, 1);
lean::inc(x_185);
lean::dec(x_110);
x_188 = lean::cnstr_get(x_183, 5);
lean::inc(x_188);
x_190 = l_list_reverse___rarg(x_188);
lean::inc(x_0);
x_192 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_190, x_2);
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
if (lean::obj_tag(x_193) == 0)
{
obj* x_203; obj* x_206; obj* x_208; obj* x_209; 
lean::dec(x_185);
lean::dec(x_183);
lean::dec(x_25);
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_57);
x_203 = lean::cnstr_get(x_192, 1);
lean::inc(x_203);
lean::dec(x_192);
x_206 = lean::cnstr_get(x_193, 0);
if (lean::is_exclusive(x_193)) {
 x_208 = x_193;
} else {
 lean::inc(x_206);
 lean::dec(x_193);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_206);
x_3 = x_209;
x_4 = x_203;
goto lbl_5;
}
else
{
obj* x_210; obj* x_211; obj* x_213; obj* x_214; obj* x_216; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
if (lean::is_exclusive(x_193)) {
 lean::cnstr_release(x_193, 0);
 x_210 = x_193;
} else {
 lean::dec(x_193);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_192, 1);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 x_213 = x_192;
} else {
 lean::inc(x_211);
 lean::dec(x_192);
 x_213 = lean::box(0);
}
x_214 = lean::cnstr_get(x_183, 6);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_183, 7);
lean::inc(x_216);
lean::dec(x_183);
x_219 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_219, 0, x_55);
lean::cnstr_set(x_219, 1, x_23);
if (lean::is_scalar(x_213)) {
 x_220 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_220 = x_213;
}
lean::cnstr_set(x_220, 0, x_216);
lean::cnstr_set(x_220, 1, x_219);
if (lean::is_scalar(x_25)) {
 x_221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_221 = x_25;
}
lean::cnstr_set(x_221, 0, x_214);
lean::cnstr_set(x_221, 1, x_220);
if (lean::is_scalar(x_20)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_20;
}
lean::cnstr_set(x_222, 0, x_185);
lean::cnstr_set(x_222, 1, x_221);
if (lean::is_scalar(x_17)) {
 x_223 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_223 = x_17;
}
lean::cnstr_set(x_223, 0, x_57);
lean::cnstr_set(x_223, 1, x_222);
x_224 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_224, 0, x_223);
if (lean::is_scalar(x_210)) {
 x_225 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_225 = x_210;
}
lean::cnstr_set(x_225, 0, x_224);
x_3 = x_225;
x_4 = x_211;
goto lbl_5;
}
}
}
}
else
{
obj* x_229; obj* x_230; obj* x_231; 
lean::dec(x_17);
lean::inc(x_62);
lean::inc(x_0);
x_229 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_62, x_2);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_230 = x_62;
} else {
 lean::dec(x_62);
 x_230 = lean::box(0);
}
x_231 = lean::cnstr_get(x_229, 0);
lean::inc(x_231);
if (lean::obj_tag(x_231) == 0)
{
obj* x_242; obj* x_245; obj* x_247; obj* x_248; 
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_230);
lean::dec(x_57);
x_242 = lean::cnstr_get(x_229, 1);
lean::inc(x_242);
lean::dec(x_229);
x_245 = lean::cnstr_get(x_231, 0);
if (lean::is_exclusive(x_231)) {
 x_247 = x_231;
} else {
 lean::inc(x_245);
 lean::dec(x_231);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_245);
x_3 = x_248;
x_4 = x_242;
goto lbl_5;
}
else
{
obj* x_250; obj* x_252; obj* x_253; obj* x_255; obj* x_256; obj* x_258; 
lean::dec(x_231);
x_250 = lean::cnstr_get(x_229, 1);
if (lean::is_exclusive(x_229)) {
 lean::cnstr_release(x_229, 0);
 lean::cnstr_set(x_229, 1, lean::box(0));
 x_252 = x_229;
} else {
 lean::inc(x_250);
 lean::dec(x_229);
 x_252 = lean::box(0);
}
x_253 = lean::cnstr_get(x_55, 0);
lean::inc(x_253);
x_255 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_255, 0, x_253);
x_256 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_256, 0, x_255);
lean::inc(x_21);
x_258 = l_lean_run__expander___rarg(x_256, x_21);
if (lean::obj_tag(x_258) == 0)
{
obj* x_259; obj* x_263; obj* x_264; 
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
lean::dec(x_258);
lean::inc(x_0);
x_263 = lean::apply_2(x_0, x_259, x_250);
x_264 = lean::cnstr_get(x_263, 0);
lean::inc(x_264);
if (lean::obj_tag(x_264) == 0)
{
obj* x_276; obj* x_279; obj* x_281; obj* x_282; 
lean::dec(x_252);
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_230);
lean::dec(x_57);
x_276 = lean::cnstr_get(x_263, 1);
lean::inc(x_276);
lean::dec(x_263);
x_279 = lean::cnstr_get(x_264, 0);
if (lean::is_exclusive(x_264)) {
 x_281 = x_264;
} else {
 lean::inc(x_279);
 lean::dec(x_264);
 x_281 = lean::box(0);
}
if (lean::is_scalar(x_281)) {
 x_282 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_282 = x_281;
}
lean::cnstr_set(x_282, 0, x_279);
x_3 = x_282;
x_4 = x_276;
goto lbl_5;
}
else
{
obj* x_283; obj* x_284; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
if (lean::is_exclusive(x_264)) {
 lean::cnstr_release(x_264, 0);
 x_283 = x_264;
} else {
 lean::dec(x_264);
 x_283 = lean::box(0);
}
x_284 = lean::cnstr_get(x_263, 1);
if (lean::is_exclusive(x_263)) {
 lean::cnstr_release(x_263, 0);
 x_286 = x_263;
} else {
 lean::inc(x_284);
 lean::dec(x_263);
 x_286 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_287 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_287 = x_230;
}
lean::cnstr_set(x_287, 0, x_55);
lean::cnstr_set(x_287, 1, x_23);
if (lean::is_scalar(x_286)) {
 x_288 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_288 = x_286;
}
lean::cnstr_set(x_288, 0, x_21);
lean::cnstr_set(x_288, 1, x_287);
if (lean::is_scalar(x_252)) {
 x_289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_289 = x_252;
}
lean::cnstr_set(x_289, 0, x_18);
lean::cnstr_set(x_289, 1, x_288);
if (lean::is_scalar(x_25)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_25;
}
lean::cnstr_set(x_290, 0, x_15);
lean::cnstr_set(x_290, 1, x_289);
if (lean::is_scalar(x_20)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_20;
}
lean::cnstr_set(x_291, 0, x_57);
lean::cnstr_set(x_291, 1, x_290);
x_292 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_292, 0, x_291);
if (lean::is_scalar(x_283)) {
 x_293 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_293 = x_283;
}
lean::cnstr_set(x_293, 0, x_292);
x_3 = x_293;
x_4 = x_284;
goto lbl_5;
}
}
else
{
obj* x_296; obj* x_299; obj* x_301; 
lean::dec(x_18);
lean::dec(x_21);
x_296 = lean::cnstr_get(x_258, 0);
lean::inc(x_296);
lean::dec(x_258);
x_299 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_299, 0, x_15);
lean::inc(x_296);
x_301 = l_lean_run__elaborator___rarg(x_299, x_296);
if (lean::obj_tag(x_301) == 0)
{
obj* x_306; obj* x_309; uint8 x_310; 
lean::dec(x_252);
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_57);
x_306 = lean::cnstr_get(x_301, 0);
lean::inc(x_306);
lean::dec(x_301);
x_309 = l_lean_parser_module_eoi;
x_310 = l_lean_parser_syntax_is__of__kind___main(x_309, x_296);
if (x_310 == 0)
{
obj* x_311; obj* x_312; obj* x_313; 
x_311 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
x_312 = l_io_println___at_lean_run__frontend___spec__3(x_311, x_250);
x_313 = lean::cnstr_get(x_312, 0);
lean::inc(x_313);
if (lean::obj_tag(x_313) == 0)
{
obj* x_319; obj* x_322; obj* x_324; obj* x_325; 
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_230);
lean::dec(x_306);
x_319 = lean::cnstr_get(x_312, 1);
lean::inc(x_319);
lean::dec(x_312);
x_322 = lean::cnstr_get(x_313, 0);
if (lean::is_exclusive(x_313)) {
 x_324 = x_313;
} else {
 lean::inc(x_322);
 lean::dec(x_313);
 x_324 = lean::box(0);
}
if (lean::is_scalar(x_324)) {
 x_325 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_325 = x_324;
}
lean::cnstr_set(x_325, 0, x_322);
x_3 = x_325;
x_4 = x_319;
goto lbl_5;
}
else
{
obj* x_327; obj* x_330; obj* x_332; obj* x_333; 
lean::dec(x_313);
x_327 = lean::cnstr_get(x_312, 1);
lean::inc(x_327);
lean::dec(x_312);
x_330 = l_list_reverse___rarg(x_306);
lean::inc(x_0);
x_332 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_330, x_327);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
if (lean::obj_tag(x_333) == 0)
{
obj* x_338; obj* x_341; obj* x_343; obj* x_344; 
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_230);
x_338 = lean::cnstr_get(x_332, 1);
lean::inc(x_338);
lean::dec(x_332);
x_341 = lean::cnstr_get(x_333, 0);
if (lean::is_exclusive(x_333)) {
 x_343 = x_333;
} else {
 lean::inc(x_341);
 lean::dec(x_333);
 x_343 = lean::box(0);
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_341);
x_3 = x_344;
x_4 = x_338;
goto lbl_5;
}
else
{
obj* x_345; obj* x_346; obj* x_349; obj* x_350; obj* x_351; obj* x_352; 
if (lean::is_exclusive(x_333)) {
 lean::cnstr_release(x_333, 0);
 x_345 = x_333;
} else {
 lean::dec(x_333);
 x_345 = lean::box(0);
}
x_346 = lean::cnstr_get(x_332, 1);
lean::inc(x_346);
lean::dec(x_332);
if (lean::is_scalar(x_230)) {
 x_349 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_349 = x_230;
}
lean::cnstr_set(x_349, 0, x_55);
lean::cnstr_set(x_349, 1, x_23);
x_350 = l_list_reverse___rarg(x_349);
x_351 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_351, 0, x_350);
if (lean::is_scalar(x_345)) {
 x_352 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_352 = x_345;
}
lean::cnstr_set(x_352, 0, x_351);
x_3 = x_352;
x_4 = x_346;
goto lbl_5;
}
}
}
else
{
obj* x_353; obj* x_355; obj* x_356; 
x_353 = l_list_reverse___rarg(x_306);
lean::inc(x_0);
x_355 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_353, x_250);
x_356 = lean::cnstr_get(x_355, 0);
lean::inc(x_356);
if (lean::obj_tag(x_356) == 0)
{
obj* x_361; obj* x_364; obj* x_366; obj* x_367; 
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_230);
x_361 = lean::cnstr_get(x_355, 1);
lean::inc(x_361);
lean::dec(x_355);
x_364 = lean::cnstr_get(x_356, 0);
if (lean::is_exclusive(x_356)) {
 x_366 = x_356;
} else {
 lean::inc(x_364);
 lean::dec(x_356);
 x_366 = lean::box(0);
}
if (lean::is_scalar(x_366)) {
 x_367 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_367 = x_366;
}
lean::cnstr_set(x_367, 0, x_364);
x_3 = x_367;
x_4 = x_361;
goto lbl_5;
}
else
{
obj* x_368; obj* x_369; obj* x_372; obj* x_373; obj* x_374; obj* x_375; 
if (lean::is_exclusive(x_356)) {
 lean::cnstr_release(x_356, 0);
 x_368 = x_356;
} else {
 lean::dec(x_356);
 x_368 = lean::box(0);
}
x_369 = lean::cnstr_get(x_355, 1);
lean::inc(x_369);
lean::dec(x_355);
if (lean::is_scalar(x_230)) {
 x_372 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_372 = x_230;
}
lean::cnstr_set(x_372, 0, x_55);
lean::cnstr_set(x_372, 1, x_23);
x_373 = l_list_reverse___rarg(x_372);
x_374 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_374, 0, x_373);
if (lean::is_scalar(x_368)) {
 x_375 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_375 = x_368;
}
lean::cnstr_set(x_375, 0, x_374);
x_3 = x_375;
x_4 = x_369;
goto lbl_5;
}
}
}
else
{
obj* x_377; obj* x_379; obj* x_382; obj* x_384; obj* x_386; obj* x_387; 
lean::dec(x_296);
x_377 = lean::cnstr_get(x_301, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_301, 1);
lean::inc(x_379);
lean::dec(x_301);
x_382 = lean::cnstr_get(x_377, 5);
lean::inc(x_382);
x_384 = l_list_reverse___rarg(x_382);
lean::inc(x_0);
x_386 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_384, x_250);
x_387 = lean::cnstr_get(x_386, 0);
lean::inc(x_387);
if (lean::obj_tag(x_387) == 0)
{
obj* x_398; obj* x_401; obj* x_403; obj* x_404; 
lean::dec(x_252);
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_230);
lean::dec(x_57);
lean::dec(x_379);
lean::dec(x_377);
x_398 = lean::cnstr_get(x_386, 1);
lean::inc(x_398);
lean::dec(x_386);
x_401 = lean::cnstr_get(x_387, 0);
if (lean::is_exclusive(x_387)) {
 x_403 = x_387;
} else {
 lean::inc(x_401);
 lean::dec(x_387);
 x_403 = lean::box(0);
}
if (lean::is_scalar(x_403)) {
 x_404 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_404 = x_403;
}
lean::cnstr_set(x_404, 0, x_401);
x_3 = x_404;
x_4 = x_398;
goto lbl_5;
}
else
{
obj* x_405; obj* x_406; obj* x_408; obj* x_409; obj* x_411; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; 
if (lean::is_exclusive(x_387)) {
 lean::cnstr_release(x_387, 0);
 x_405 = x_387;
} else {
 lean::dec(x_387);
 x_405 = lean::box(0);
}
x_406 = lean::cnstr_get(x_386, 1);
if (lean::is_exclusive(x_386)) {
 lean::cnstr_release(x_386, 0);
 x_408 = x_386;
} else {
 lean::inc(x_406);
 lean::dec(x_386);
 x_408 = lean::box(0);
}
x_409 = lean::cnstr_get(x_377, 6);
lean::inc(x_409);
x_411 = lean::cnstr_get(x_377, 7);
lean::inc(x_411);
lean::dec(x_377);
if (lean::is_scalar(x_230)) {
 x_414 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_414 = x_230;
}
lean::cnstr_set(x_414, 0, x_55);
lean::cnstr_set(x_414, 1, x_23);
if (lean::is_scalar(x_408)) {
 x_415 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_415 = x_408;
}
lean::cnstr_set(x_415, 0, x_411);
lean::cnstr_set(x_415, 1, x_414);
if (lean::is_scalar(x_252)) {
 x_416 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_416 = x_252;
}
lean::cnstr_set(x_416, 0, x_409);
lean::cnstr_set(x_416, 1, x_415);
if (lean::is_scalar(x_25)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_25;
}
lean::cnstr_set(x_417, 0, x_379);
lean::cnstr_set(x_417, 1, x_416);
if (lean::is_scalar(x_20)) {
 x_418 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_418 = x_20;
}
lean::cnstr_set(x_418, 0, x_57);
lean::cnstr_set(x_418, 1, x_417);
x_419 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_419, 0, x_418);
if (lean::is_scalar(x_405)) {
 x_420 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_420 = x_405;
}
lean::cnstr_set(x_420, 0, x_419);
x_3 = x_420;
x_4 = x_406;
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
obj* x_422; obj* x_424; obj* x_425; obj* x_426; 
lean::dec(x_0);
x_422 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_424 = x_3;
} else {
 lean::inc(x_422);
 lean::dec(x_3);
 x_424 = lean::box(0);
}
if (lean::is_scalar(x_424)) {
 x_425 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_425 = x_424;
}
lean::cnstr_set(x_425, 0, x_422);
x_426 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_426, 0, x_425);
lean::cnstr_set(x_426, 1, x_4);
return x_426;
}
else
{
obj* x_427; obj* x_429; 
x_427 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_429 = x_3;
} else {
 lean::inc(x_427);
 lean::dec(x_3);
 x_429 = lean::box(0);
}
if (lean::obj_tag(x_427) == 0)
{
obj* x_431; 
lean::dec(x_429);
x_431 = lean::cnstr_get(x_427, 0);
lean::inc(x_431);
lean::dec(x_427);
x_1 = x_431;
x_2 = x_4;
goto _start;
}
else
{
obj* x_436; obj* x_439; obj* x_440; 
lean::dec(x_0);
x_436 = lean::cnstr_get(x_427, 0);
lean::inc(x_436);
lean::dec(x_427);
if (lean::is_scalar(x_429)) {
 x_439 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_439 = x_429;
}
lean::cnstr_set(x_439, 0, x_436);
x_440 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_440, 0, x_439);
lean::cnstr_set(x_440, 1, x_4);
return x_440;
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
obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; 
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
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_28 = x_25;
} else {
 lean::inc(x_26);
 lean::dec(x_25);
 x_28 = lean::box(0);
}
x_29 = 0;
x_30 = lean::box(x_29);
if (lean::is_scalar(x_28)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_28;
}
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
obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; 
lean::dec(x_16);
x_35 = l_string_quote(x_13);
x_36 = l_lean_process__file___closed__1;
x_37 = lean::string_append(x_36, x_35);
lean::dec(x_35);
x_39 = l_lean_process__file___lambda__1___closed__7;
x_40 = lean::string_append(x_37, x_39);
x_41 = l_io_println___at_lean_run__frontend___spec__3(x_40, x_10);
x_42 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_44 = x_41;
} else {
 lean::inc(x_42);
 lean::dec(x_41);
 x_44 = lean::box(0);
}
x_45 = 0;
x_46 = lean::box(x_45);
if (lean::is_scalar(x_44)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_44;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_42);
return x_47;
}
}
else
{
obj* x_50; obj* x_52; uint8 x_53; obj* x_54; obj* x_55; 
lean::dec(x_8);
lean::dec(x_0);
x_50 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_52 = x_7;
} else {
 lean::inc(x_50);
 lean::dec(x_7);
 x_52 = lean::box(0);
}
x_53 = 1;
x_54 = lean::box(x_53);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
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

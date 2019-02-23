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
obj* l_lean_mk__config___boxed(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed(obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_lean_run__parser___boxed(obj*, obj*);
extern obj* l_lean_parser_module_tokens;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___boxed(obj*, obj*);
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__6;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(obj*, obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_string_quote(obj*);
obj* l_coroutine_resume___rarg(obj*, obj*);
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_run__expander(obj*, obj*);
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
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_lean_run__elaborator___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj*, obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1;
obj* l_lean_elaborator_run(obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_run__parser(obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_reader__t_run___rarg(obj*, obj*);
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(obj*, obj*, obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1___boxed(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14(obj*, obj*, obj*);
extern obj* l_lean_parser_run___rarg___closed__1;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
obj* l_lean_run__expander___boxed(obj*, obj*);
obj* l_lean_file__map_from__string(obj*);
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_lean_run__expander___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_io_print___at_lean_run__frontend___spec__4(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_io_println___at_lean_run__frontend___spec__3(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_lean_run__elaborator(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2;
obj* l_io_print___at_lean_run__frontend___spec__4___boxed(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_run__elaborator___boxed(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1(obj*);
obj* l_lean_run__parser___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1;
obj* l___private_init_io_12__put__str___at_lean_run__frontend___spec__5___boxed(obj*, obj*);
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__4;
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
obj* x_15; obj* x_17; obj* x_18; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_17 = x_13;
} else {
 lean::inc(x_15);
 lean::dec(x_13);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_19 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_21 = x_13;
} else {
 lean::inc(x_19);
 lean::dec(x_13);
 x_21 = lean::box(0);
}
lean::inc(x_1);
x_23 = l_lean_file__map_from__string(x_1);
lean::inc(x_0);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_23);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_19);
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
if (lean::is_scalar(x_21)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_21;
}
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
}
obj* l_lean_mk__config___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_mk__config(x_0, x_1);
lean::dec(x_0);
return x_2;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__parser___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_run__parser___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_run__parser(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__expander___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_run__expander___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_run__expander(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__elaborator___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_run__elaborator___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_run__elaborator(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* x_5; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
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
x_14 = lean::cnstr_get(x_13, 0);
x_15 = lean::cnstr_get(x_14, 0);
x_16 = l_lean_parser_message__of__parsec__message___rarg(x_15, x_5);
x_17 = l_lean_message__log_empty;
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
if (lean::is_scalar(x_4)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_4;
}
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_20, 0, x_19);
return x_20;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_4);
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::cnstr_get(x_22, 0);
x_27 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_25);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_27);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2___boxed), 2, 1);
lean::closure_set(x_32, 0, x_31);
return x_32;
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
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1___boxed), 2, 1);
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
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parser died!!");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2() {
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
x_36 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1;
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
lean::dec(x_105);
if (x_119 == 0)
{
obj* x_121; obj* x_122; obj* x_123; 
x_121 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2;
x_122 = l_io_println___at_lean_run__frontend___spec__3(x_121, x_2);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_128; obj* x_131; obj* x_133; obj* x_134; 
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_115);
x_128 = lean::cnstr_get(x_122, 1);
lean::inc(x_128);
lean::dec(x_122);
x_131 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_133 = x_123;
} else {
 lean::inc(x_131);
 lean::dec(x_123);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_131);
x_3 = x_134;
x_4 = x_128;
goto lbl_5;
}
else
{
obj* x_136; obj* x_139; obj* x_141; obj* x_142; 
lean::dec(x_123);
x_136 = lean::cnstr_get(x_122, 1);
lean::inc(x_136);
lean::dec(x_122);
x_139 = l_list_reverse___rarg(x_115);
lean::inc(x_0);
x_141 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__6(x_0, x_139, x_136);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
if (lean::obj_tag(x_142) == 0)
{
obj* x_146; obj* x_149; obj* x_151; obj* x_152; 
lean::dec(x_55);
lean::dec(x_23);
x_146 = lean::cnstr_get(x_141, 1);
lean::inc(x_146);
lean::dec(x_141);
x_149 = lean::cnstr_get(x_142, 0);
if (lean::is_exclusive(x_142)) {
 x_151 = x_142;
} else {
 lean::inc(x_149);
 lean::dec(x_142);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
x_3 = x_152;
x_4 = x_146;
goto lbl_5;
}
else
{
obj* x_153; obj* x_154; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 x_153 = x_142;
} else {
 lean::dec(x_142);
 x_153 = lean::box(0);
}
x_154 = lean::cnstr_get(x_141, 1);
lean::inc(x_154);
lean::dec(x_141);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_55);
lean::cnstr_set(x_157, 1, x_23);
x_158 = l_list_reverse___rarg(x_157);
x_159 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_159, 0, x_158);
if (lean::is_scalar(x_153)) {
 x_160 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_160 = x_153;
}
lean::cnstr_set(x_160, 0, x_159);
x_3 = x_160;
x_4 = x_154;
goto lbl_5;
}
}
}
else
{
obj* x_161; obj* x_163; obj* x_164; 
x_161 = l_list_reverse___rarg(x_115);
lean::inc(x_0);
x_163 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_161, x_2);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
if (lean::obj_tag(x_164) == 0)
{
obj* x_168; obj* x_171; obj* x_173; obj* x_174; 
lean::dec(x_55);
lean::dec(x_23);
x_168 = lean::cnstr_get(x_163, 1);
lean::inc(x_168);
lean::dec(x_163);
x_171 = lean::cnstr_get(x_164, 0);
if (lean::is_exclusive(x_164)) {
 x_173 = x_164;
} else {
 lean::inc(x_171);
 lean::dec(x_164);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
x_3 = x_174;
x_4 = x_168;
goto lbl_5;
}
else
{
obj* x_175; obj* x_176; obj* x_179; obj* x_180; obj* x_181; obj* x_182; 
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 x_175 = x_164;
} else {
 lean::dec(x_164);
 x_175 = lean::box(0);
}
x_176 = lean::cnstr_get(x_163, 1);
lean::inc(x_176);
lean::dec(x_163);
x_179 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_179, 0, x_55);
lean::cnstr_set(x_179, 1, x_23);
x_180 = l_list_reverse___rarg(x_179);
x_181 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_181, 0, x_180);
if (lean::is_scalar(x_175)) {
 x_182 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_182 = x_175;
}
lean::cnstr_set(x_182, 0, x_181);
x_3 = x_182;
x_4 = x_176;
goto lbl_5;
}
}
}
else
{
obj* x_184; obj* x_186; obj* x_189; obj* x_191; obj* x_193; obj* x_194; 
lean::dec(x_105);
x_184 = lean::cnstr_get(x_110, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_110, 1);
lean::inc(x_186);
lean::dec(x_110);
x_189 = lean::cnstr_get(x_184, 5);
lean::inc(x_189);
x_191 = l_list_reverse___rarg(x_189);
lean::inc(x_0);
x_193 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_191, x_2);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
if (lean::obj_tag(x_194) == 0)
{
obj* x_204; obj* x_207; obj* x_209; obj* x_210; 
lean::dec(x_184);
lean::dec(x_186);
lean::dec(x_25);
lean::dec(x_17);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_57);
x_204 = lean::cnstr_get(x_193, 1);
lean::inc(x_204);
lean::dec(x_193);
x_207 = lean::cnstr_get(x_194, 0);
if (lean::is_exclusive(x_194)) {
 x_209 = x_194;
} else {
 lean::inc(x_207);
 lean::dec(x_194);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_207);
x_3 = x_210;
x_4 = x_204;
goto lbl_5;
}
else
{
obj* x_211; obj* x_212; obj* x_214; obj* x_215; obj* x_217; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 x_211 = x_194;
} else {
 lean::dec(x_194);
 x_211 = lean::box(0);
}
x_212 = lean::cnstr_get(x_193, 1);
if (lean::is_exclusive(x_193)) {
 lean::cnstr_release(x_193, 0);
 x_214 = x_193;
} else {
 lean::inc(x_212);
 lean::dec(x_193);
 x_214 = lean::box(0);
}
x_215 = lean::cnstr_get(x_184, 6);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_184, 7);
lean::inc(x_217);
lean::dec(x_184);
x_220 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_220, 0, x_55);
lean::cnstr_set(x_220, 1, x_23);
if (lean::is_scalar(x_214)) {
 x_221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_221 = x_214;
}
lean::cnstr_set(x_221, 0, x_217);
lean::cnstr_set(x_221, 1, x_220);
if (lean::is_scalar(x_25)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_25;
}
lean::cnstr_set(x_222, 0, x_215);
lean::cnstr_set(x_222, 1, x_221);
if (lean::is_scalar(x_20)) {
 x_223 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_223 = x_20;
}
lean::cnstr_set(x_223, 0, x_186);
lean::cnstr_set(x_223, 1, x_222);
if (lean::is_scalar(x_17)) {
 x_224 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_224 = x_17;
}
lean::cnstr_set(x_224, 0, x_57);
lean::cnstr_set(x_224, 1, x_223);
x_225 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_225, 0, x_224);
if (lean::is_scalar(x_211)) {
 x_226 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_226 = x_211;
}
lean::cnstr_set(x_226, 0, x_225);
x_3 = x_226;
x_4 = x_212;
goto lbl_5;
}
}
}
}
else
{
obj* x_230; obj* x_231; obj* x_232; 
lean::dec(x_17);
lean::inc(x_62);
lean::inc(x_0);
x_230 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_62, x_2);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_231 = x_62;
} else {
 lean::dec(x_62);
 x_231 = lean::box(0);
}
x_232 = lean::cnstr_get(x_230, 0);
lean::inc(x_232);
if (lean::obj_tag(x_232) == 0)
{
obj* x_243; obj* x_246; obj* x_248; obj* x_249; 
lean::dec(x_231);
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_57);
x_243 = lean::cnstr_get(x_230, 1);
lean::inc(x_243);
lean::dec(x_230);
x_246 = lean::cnstr_get(x_232, 0);
if (lean::is_exclusive(x_232)) {
 x_248 = x_232;
} else {
 lean::inc(x_246);
 lean::dec(x_232);
 x_248 = lean::box(0);
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_246);
x_3 = x_249;
x_4 = x_243;
goto lbl_5;
}
else
{
obj* x_251; obj* x_253; obj* x_254; obj* x_256; obj* x_257; obj* x_259; 
lean::dec(x_232);
x_251 = lean::cnstr_get(x_230, 1);
if (lean::is_exclusive(x_230)) {
 lean::cnstr_release(x_230, 0);
 lean::cnstr_set(x_230, 1, lean::box(0));
 x_253 = x_230;
} else {
 lean::inc(x_251);
 lean::dec(x_230);
 x_253 = lean::box(0);
}
x_254 = lean::cnstr_get(x_55, 0);
lean::inc(x_254);
x_256 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_256, 0, x_254);
x_257 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_257, 0, x_256);
lean::inc(x_21);
x_259 = l_lean_run__expander___rarg(x_257, x_21);
if (lean::obj_tag(x_259) == 0)
{
obj* x_260; obj* x_264; obj* x_265; 
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
lean::dec(x_259);
lean::inc(x_0);
x_264 = lean::apply_2(x_0, x_260, x_251);
x_265 = lean::cnstr_get(x_264, 0);
lean::inc(x_265);
if (lean::obj_tag(x_265) == 0)
{
obj* x_277; obj* x_280; obj* x_282; obj* x_283; 
lean::dec(x_231);
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_23);
lean::dec(x_253);
lean::dec(x_57);
x_277 = lean::cnstr_get(x_264, 1);
lean::inc(x_277);
lean::dec(x_264);
x_280 = lean::cnstr_get(x_265, 0);
if (lean::is_exclusive(x_265)) {
 x_282 = x_265;
} else {
 lean::inc(x_280);
 lean::dec(x_265);
 x_282 = lean::box(0);
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_280);
x_3 = x_283;
x_4 = x_277;
goto lbl_5;
}
else
{
obj* x_284; obj* x_285; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
if (lean::is_exclusive(x_265)) {
 lean::cnstr_release(x_265, 0);
 x_284 = x_265;
} else {
 lean::dec(x_265);
 x_284 = lean::box(0);
}
x_285 = lean::cnstr_get(x_264, 1);
if (lean::is_exclusive(x_264)) {
 lean::cnstr_release(x_264, 0);
 x_287 = x_264;
} else {
 lean::inc(x_285);
 lean::dec(x_264);
 x_287 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_288 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_288 = x_231;
}
lean::cnstr_set(x_288, 0, x_55);
lean::cnstr_set(x_288, 1, x_23);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_21);
lean::cnstr_set(x_289, 1, x_288);
if (lean::is_scalar(x_253)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_253;
}
lean::cnstr_set(x_290, 0, x_18);
lean::cnstr_set(x_290, 1, x_289);
if (lean::is_scalar(x_25)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_25;
}
lean::cnstr_set(x_291, 0, x_15);
lean::cnstr_set(x_291, 1, x_290);
if (lean::is_scalar(x_20)) {
 x_292 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_292 = x_20;
}
lean::cnstr_set(x_292, 0, x_57);
lean::cnstr_set(x_292, 1, x_291);
x_293 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_293, 0, x_292);
if (lean::is_scalar(x_284)) {
 x_294 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_294 = x_284;
}
lean::cnstr_set(x_294, 0, x_293);
x_3 = x_294;
x_4 = x_285;
goto lbl_5;
}
}
else
{
obj* x_297; obj* x_300; obj* x_302; 
lean::dec(x_18);
lean::dec(x_21);
x_297 = lean::cnstr_get(x_259, 0);
lean::inc(x_297);
lean::dec(x_259);
x_300 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_300, 0, x_15);
lean::inc(x_297);
x_302 = l_lean_run__elaborator___rarg(x_300, x_297);
if (lean::obj_tag(x_302) == 0)
{
obj* x_307; obj* x_310; uint8 x_311; 
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_253);
lean::dec(x_57);
x_307 = lean::cnstr_get(x_302, 0);
lean::inc(x_307);
lean::dec(x_302);
x_310 = l_lean_parser_module_eoi;
x_311 = l_lean_parser_syntax_is__of__kind___main(x_310, x_297);
lean::dec(x_297);
if (x_311 == 0)
{
obj* x_313; obj* x_314; obj* x_315; 
x_313 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2;
x_314 = l_io_println___at_lean_run__frontend___spec__3(x_313, x_251);
x_315 = lean::cnstr_get(x_314, 0);
lean::inc(x_315);
if (lean::obj_tag(x_315) == 0)
{
obj* x_321; obj* x_324; obj* x_326; obj* x_327; 
lean::dec(x_231);
lean::dec(x_307);
lean::dec(x_55);
lean::dec(x_23);
x_321 = lean::cnstr_get(x_314, 1);
lean::inc(x_321);
lean::dec(x_314);
x_324 = lean::cnstr_get(x_315, 0);
if (lean::is_exclusive(x_315)) {
 x_326 = x_315;
} else {
 lean::inc(x_324);
 lean::dec(x_315);
 x_326 = lean::box(0);
}
if (lean::is_scalar(x_326)) {
 x_327 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_327 = x_326;
}
lean::cnstr_set(x_327, 0, x_324);
x_3 = x_327;
x_4 = x_321;
goto lbl_5;
}
else
{
obj* x_329; obj* x_332; obj* x_334; obj* x_335; 
lean::dec(x_315);
x_329 = lean::cnstr_get(x_314, 1);
lean::inc(x_329);
lean::dec(x_314);
x_332 = l_list_reverse___rarg(x_307);
lean::inc(x_0);
x_334 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_332, x_329);
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
if (lean::obj_tag(x_335) == 0)
{
obj* x_340; obj* x_343; obj* x_345; obj* x_346; 
lean::dec(x_231);
lean::dec(x_55);
lean::dec(x_23);
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
if (lean::is_scalar(x_231)) {
 x_351 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_351 = x_231;
}
lean::cnstr_set(x_351, 0, x_55);
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
obj* x_355; obj* x_357; obj* x_358; 
x_355 = l_list_reverse___rarg(x_307);
lean::inc(x_0);
x_357 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_355, x_251);
x_358 = lean::cnstr_get(x_357, 0);
lean::inc(x_358);
if (lean::obj_tag(x_358) == 0)
{
obj* x_363; obj* x_366; obj* x_368; obj* x_369; 
lean::dec(x_231);
lean::dec(x_55);
lean::dec(x_23);
x_363 = lean::cnstr_get(x_357, 1);
lean::inc(x_363);
lean::dec(x_357);
x_366 = lean::cnstr_get(x_358, 0);
if (lean::is_exclusive(x_358)) {
 x_368 = x_358;
} else {
 lean::inc(x_366);
 lean::dec(x_358);
 x_368 = lean::box(0);
}
if (lean::is_scalar(x_368)) {
 x_369 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_369 = x_368;
}
lean::cnstr_set(x_369, 0, x_366);
x_3 = x_369;
x_4 = x_363;
goto lbl_5;
}
else
{
obj* x_370; obj* x_371; obj* x_374; obj* x_375; obj* x_376; obj* x_377; 
if (lean::is_exclusive(x_358)) {
 lean::cnstr_release(x_358, 0);
 x_370 = x_358;
} else {
 lean::dec(x_358);
 x_370 = lean::box(0);
}
x_371 = lean::cnstr_get(x_357, 1);
lean::inc(x_371);
lean::dec(x_357);
if (lean::is_scalar(x_231)) {
 x_374 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_374 = x_231;
}
lean::cnstr_set(x_374, 0, x_55);
lean::cnstr_set(x_374, 1, x_23);
x_375 = l_list_reverse___rarg(x_374);
x_376 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_376, 0, x_375);
if (lean::is_scalar(x_370)) {
 x_377 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_377 = x_370;
}
lean::cnstr_set(x_377, 0, x_376);
x_3 = x_377;
x_4 = x_371;
goto lbl_5;
}
}
}
else
{
obj* x_379; obj* x_381; obj* x_384; obj* x_386; obj* x_388; obj* x_389; 
lean::dec(x_297);
x_379 = lean::cnstr_get(x_302, 0);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_302, 1);
lean::inc(x_381);
lean::dec(x_302);
x_384 = lean::cnstr_get(x_379, 5);
lean::inc(x_384);
x_386 = l_list_reverse___rarg(x_384);
lean::inc(x_0);
x_388 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_386, x_251);
x_389 = lean::cnstr_get(x_388, 0);
lean::inc(x_389);
if (lean::obj_tag(x_389) == 0)
{
obj* x_400; obj* x_403; obj* x_405; obj* x_406; 
lean::dec(x_231);
lean::dec(x_25);
lean::dec(x_20);
lean::dec(x_55);
lean::dec(x_23);
lean::dec(x_253);
lean::dec(x_57);
lean::dec(x_381);
lean::dec(x_379);
x_400 = lean::cnstr_get(x_388, 1);
lean::inc(x_400);
lean::dec(x_388);
x_403 = lean::cnstr_get(x_389, 0);
if (lean::is_exclusive(x_389)) {
 x_405 = x_389;
} else {
 lean::inc(x_403);
 lean::dec(x_389);
 x_405 = lean::box(0);
}
if (lean::is_scalar(x_405)) {
 x_406 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_406 = x_405;
}
lean::cnstr_set(x_406, 0, x_403);
x_3 = x_406;
x_4 = x_400;
goto lbl_5;
}
else
{
obj* x_407; obj* x_408; obj* x_410; obj* x_411; obj* x_413; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_421; obj* x_422; 
if (lean::is_exclusive(x_389)) {
 lean::cnstr_release(x_389, 0);
 x_407 = x_389;
} else {
 lean::dec(x_389);
 x_407 = lean::box(0);
}
x_408 = lean::cnstr_get(x_388, 1);
if (lean::is_exclusive(x_388)) {
 lean::cnstr_release(x_388, 0);
 x_410 = x_388;
} else {
 lean::inc(x_408);
 lean::dec(x_388);
 x_410 = lean::box(0);
}
x_411 = lean::cnstr_get(x_379, 6);
lean::inc(x_411);
x_413 = lean::cnstr_get(x_379, 7);
lean::inc(x_413);
lean::dec(x_379);
if (lean::is_scalar(x_231)) {
 x_416 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_416 = x_231;
}
lean::cnstr_set(x_416, 0, x_55);
lean::cnstr_set(x_416, 1, x_23);
if (lean::is_scalar(x_410)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_410;
}
lean::cnstr_set(x_417, 0, x_413);
lean::cnstr_set(x_417, 1, x_416);
if (lean::is_scalar(x_253)) {
 x_418 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_418 = x_253;
}
lean::cnstr_set(x_418, 0, x_411);
lean::cnstr_set(x_418, 1, x_417);
if (lean::is_scalar(x_25)) {
 x_419 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_419 = x_25;
}
lean::cnstr_set(x_419, 0, x_381);
lean::cnstr_set(x_419, 1, x_418);
if (lean::is_scalar(x_20)) {
 x_420 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_420 = x_20;
}
lean::cnstr_set(x_420, 0, x_57);
lean::cnstr_set(x_420, 1, x_419);
x_421 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_421, 0, x_420);
if (lean::is_scalar(x_407)) {
 x_422 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_422 = x_407;
}
lean::cnstr_set(x_422, 0, x_421);
x_3 = x_422;
x_4 = x_408;
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
obj* x_424; obj* x_426; obj* x_427; obj* x_428; 
lean::dec(x_0);
x_424 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_426 = x_3;
} else {
 lean::inc(x_424);
 lean::dec(x_3);
 x_426 = lean::box(0);
}
if (lean::is_scalar(x_426)) {
 x_427 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_427 = x_426;
}
lean::cnstr_set(x_427, 0, x_424);
x_428 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_428, 0, x_427);
lean::cnstr_set(x_428, 1, x_4);
return x_428;
}
else
{
obj* x_429; obj* x_431; 
x_429 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_431 = x_3;
} else {
 lean::inc(x_429);
 lean::dec(x_3);
 x_431 = lean::box(0);
}
if (lean::obj_tag(x_429) == 0)
{
obj* x_433; 
lean::dec(x_431);
x_433 = lean::cnstr_get(x_429, 0);
lean::inc(x_433);
lean::dec(x_429);
x_1 = x_433;
x_2 = x_4;
goto _start;
}
else
{
obj* x_438; obj* x_441; obj* x_442; 
lean::dec(x_0);
x_438 = lean::cnstr_get(x_429, 0);
lean::inc(x_438);
lean::dec(x_429);
if (lean::is_scalar(x_431)) {
 x_441 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_441 = x_431;
}
lean::cnstr_set(x_441, 0, x_438);
x_442 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_442, 0, x_441);
lean::cnstr_set(x_442, 1, x_4);
return x_442;
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
obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::inc(x_1);
x_6 = l_lean_file__map_from__string(x_1);
lean::inc(x_1);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_6);
x_10 = l_lean_expander_builtin__transformers;
lean::inc(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___closed__1;
lean::inc(x_4);
x_15 = l_lean_parser_run___at_lean_run__frontend___spec__1(x_4, x_1, x_13);
lean::inc(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_4);
x_18 = l_lean_elaborator_run(x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_io_prim_iterate___main___at_lean_run__frontend___spec__14(x_2, x_23, x_3);
return x_24;
}
}
obj* l_lean_run__frontend(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
lean::inc(x_1);
x_8 = l_lean_mk__config(x_0, x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_11 = x_8;
} else {
 lean::inc(x_9);
 lean::dec(x_8);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
lean::inc(x_3);
x_4 = x_12;
x_5 = x_3;
goto lbl_6;
}
else
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_16 = x_8;
} else {
 lean::inc(x_14);
 lean::dec(x_8);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
lean::inc(x_3);
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
x_29 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(x_0, x_1, x_2, x_5, x_26);
return x_29;
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
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(x_0, x_1);
lean::dec(x_0);
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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__13(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_lean_run__frontend___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_run__frontend(x_0, x_1, x_2, x_3);
lean::dec(x_0);
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
obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
x_4 = lean::box(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_lean_run__frontend(x_0, x_1, x_5, x_3);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
if (x_2 == 0)
{
obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; 
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
lean::dec(x_24);
x_27 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_29 = x_25;
} else {
 lean::inc(x_27);
 lean::dec(x_25);
 x_29 = lean::box(0);
}
x_30 = 0;
x_31 = lean::box(x_30);
if (lean::is_scalar(x_29)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_29;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_27);
return x_32;
}
else
{
obj* x_34; 
lean::dec(x_0);
x_34 = lean::box(0);
x_16 = x_34;
goto lbl_17;
}
lbl_17:
{
obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; 
lean::dec(x_16);
x_36 = l_string_quote(x_13);
x_37 = l_lean_process__file___closed__1;
x_38 = lean::string_append(x_37, x_36);
lean::dec(x_36);
x_40 = l_lean_process__file___lambda__1___closed__7;
x_41 = lean::string_append(x_38, x_40);
x_42 = l_io_println___at_lean_run__frontend___spec__3(x_41, x_10);
lean::dec(x_41);
x_44 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_46 = x_42;
} else {
 lean::inc(x_44);
 lean::dec(x_42);
 x_46 = lean::box(0);
}
x_47 = 0;
x_48 = lean::box(x_47);
if (lean::is_scalar(x_46)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_46;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
return x_49;
}
}
else
{
obj* x_52; obj* x_54; uint8 x_55; obj* x_56; obj* x_57; 
lean::dec(x_8);
lean::dec(x_0);
x_52 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_54 = x_6;
} else {
 lean::inc(x_52);
 lean::dec(x_6);
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
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_run__frontend___spec__6___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__1);
 l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2();
lean::mark_persistent(l_io_prim_iterate___main___at_lean_run__frontend___spec__14___closed__2);
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

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
obj* x_1; obj* x_3; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_5 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
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
obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_5)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_5;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_3);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_17, 0, x_16);
return x_17;
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
if (lean::is_scalar(x_4)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_4;
}
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
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_15 = x_3;
} else {
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
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
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_2 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
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
obj* x_15; obj* x_16; 
lean::dec(x_7);
lean::dec(x_3);
x_15 = l_lean_format_be___main___closed__1;
x_16 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_15, x_5);
return x_16;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_2(x_0, x_6, x_2);
x_13 = lean::cnstr_get(x_12, 0);
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 x_17 = x_12;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_0);
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
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_1 = x_8;
x_2 = x_15;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_28; 
x_6 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 x_10 = x_1;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_15 = x_8;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_13, 0);
x_18 = lean::cnstr_get(x_13, 1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 lean::cnstr_set(x_13, 1, lean::box(0));
 x_20 = x_13;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_13);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_18, 0);
x_23 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 lean::cnstr_set(x_18, 1, lean::box(0));
 x_25 = x_18;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_18);
 x_25 = lean::box(0);
}
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_26, 0, x_6);
lean::inc(x_16);
x_28 = l_lean_run__parser___rarg(x_26, x_16);
if (lean::obj_tag(x_28) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_28);
x_37 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
x_38 = l_io_println___at_lean_run__frontend___spec__3(x_37, x_2);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_23);
x_45 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_47 = x_39;
} else {
 lean::inc(x_45);
 lean::dec(x_39);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
x_3 = x_48;
x_4 = x_41;
goto lbl_5;
}
else
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_49 = x_39;
} else {
 lean::dec(x_39);
 x_49 = lean::box(0);
}
x_50 = l_list_reverse___rarg(x_23);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
if (lean::is_scalar(x_49)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_49;
}
lean::cnstr_set(x_52, 0, x_51);
x_3 = x_52;
x_4 = x_41;
goto lbl_5;
}
}
else
{
obj* x_53; obj* x_55; obj* x_58; obj* x_60; 
x_53 = lean::cnstr_get(x_28, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_28, 1);
lean::inc(x_55);
lean::dec(x_28);
x_58 = lean::cnstr_get(x_53, 1);
lean::inc(x_58);
x_60 = l_list_reverse___rarg(x_58);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; 
x_61 = lean::cnstr_get(x_53, 0);
lean::inc(x_61);
x_63 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_63, 0, x_61);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_64, 0, x_63);
lean::inc(x_21);
x_66 = l_lean_run__expander___rarg(x_64, x_21);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_74; 
x_67 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_69 = x_66;
} else {
 lean::inc(x_67);
 lean::dec(x_66);
 x_69 = lean::box(0);
}
lean::inc(x_0);
x_71 = lean::apply_2(x_0, x_67, x_2);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_87; obj* x_90; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_53);
lean::dec(x_55);
x_87 = lean::cnstr_get(x_72, 0);
lean::inc(x_87);
lean::dec(x_72);
if (lean::is_scalar(x_69)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_69;
}
lean::cnstr_set(x_90, 0, x_87);
x_3 = x_90;
x_4 = x_74;
goto lbl_5;
}
else
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_72);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_53);
lean::cnstr_set(x_92, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_10;
}
lean::cnstr_set(x_93, 0, x_21);
lean::cnstr_set(x_93, 1, x_92);
if (lean::is_scalar(x_15)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_15;
}
lean::cnstr_set(x_94, 0, x_16);
lean::cnstr_set(x_94, 1, x_93);
if (lean::is_scalar(x_20)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_20;
}
lean::cnstr_set(x_95, 0, x_11);
lean::cnstr_set(x_95, 1, x_94);
if (lean::is_scalar(x_25)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_25;
}
lean::cnstr_set(x_96, 0, x_55);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
if (lean::is_scalar(x_69)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_69;
 lean::cnstr_set_tag(x_69, 1);
}
lean::cnstr_set(x_98, 0, x_97);
x_3 = x_98;
x_4 = x_74;
goto lbl_5;
}
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; 
lean::dec(x_16);
lean::dec(x_21);
x_101 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_set(x_66, 0, lean::box(0));
 x_103 = x_66;
} else {
 lean::inc(x_101);
 lean::dec(x_66);
 x_103 = lean::box(0);
}
x_104 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_104, 0, x_11);
lean::inc(x_101);
x_106 = l_lean_run__elaborator___rarg(x_104, x_101);
if (lean::obj_tag(x_106) == 0)
{
obj* x_112; obj* x_115; uint8 x_116; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_55);
x_112 = lean::cnstr_get(x_106, 0);
lean::inc(x_112);
lean::dec(x_106);
x_115 = l_lean_parser_module_eoi;
x_116 = l_lean_parser_syntax_is__of__kind___main(x_115, x_101);
if (x_116 == 0)
{
obj* x_117; obj* x_118; obj* x_119; obj* x_121; 
x_117 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
x_118 = l_io_println___at_lean_run__frontend___spec__3(x_117, x_2);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
lean::dec(x_118);
if (lean::obj_tag(x_119) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_23);
lean::dec(x_53);
lean::dec(x_112);
x_127 = lean::cnstr_get(x_119, 0);
lean::inc(x_127);
lean::dec(x_119);
if (lean::is_scalar(x_103)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_130, 0, x_127);
x_3 = x_130;
x_4 = x_121;
goto lbl_5;
}
else
{
obj* x_132; obj* x_134; obj* x_135; obj* x_137; 
lean::dec(x_119);
x_132 = l_list_reverse___rarg(x_112);
lean::inc(x_0);
x_134 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_132, x_121);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
lean::dec(x_134);
if (lean::obj_tag(x_135) == 0)
{
obj* x_142; obj* x_145; 
lean::dec(x_23);
lean::dec(x_53);
x_142 = lean::cnstr_get(x_135, 0);
lean::inc(x_142);
lean::dec(x_135);
if (lean::is_scalar(x_103)) {
 x_145 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_145 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_145, 0, x_142);
x_3 = x_145;
x_4 = x_137;
goto lbl_5;
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_135);
x_147 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_147, 0, x_53);
lean::cnstr_set(x_147, 1, x_23);
x_148 = l_list_reverse___rarg(x_147);
x_149 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_149, 0, x_148);
if (lean::is_scalar(x_103)) {
 x_150 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_150 = x_103;
}
lean::cnstr_set(x_150, 0, x_149);
x_3 = x_150;
x_4 = x_137;
goto lbl_5;
}
}
}
else
{
obj* x_151; obj* x_153; obj* x_154; obj* x_156; 
x_151 = l_list_reverse___rarg(x_112);
lean::inc(x_0);
x_153 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_151, x_2);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_153, 1);
lean::inc(x_156);
lean::dec(x_153);
if (lean::obj_tag(x_154) == 0)
{
obj* x_161; obj* x_164; 
lean::dec(x_23);
lean::dec(x_53);
x_161 = lean::cnstr_get(x_154, 0);
lean::inc(x_161);
lean::dec(x_154);
if (lean::is_scalar(x_103)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_164, 0, x_161);
x_3 = x_164;
x_4 = x_156;
goto lbl_5;
}
else
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_154);
x_166 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_166, 0, x_53);
lean::cnstr_set(x_166, 1, x_23);
x_167 = l_list_reverse___rarg(x_166);
x_168 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_168, 0, x_167);
if (lean::is_scalar(x_103)) {
 x_169 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_169 = x_103;
}
lean::cnstr_set(x_169, 0, x_168);
x_3 = x_169;
x_4 = x_156;
goto lbl_5;
}
}
}
else
{
obj* x_171; obj* x_173; obj* x_176; obj* x_178; obj* x_180; obj* x_181; obj* x_183; 
lean::dec(x_101);
x_171 = lean::cnstr_get(x_106, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_106, 1);
lean::inc(x_173);
lean::dec(x_106);
x_176 = lean::cnstr_get(x_171, 5);
lean::inc(x_176);
x_178 = l_list_reverse___rarg(x_176);
lean::inc(x_0);
x_180 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_178, x_2);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
lean::dec(x_180);
if (lean::obj_tag(x_181) == 0)
{
obj* x_195; obj* x_198; 
lean::dec(x_173);
lean::dec(x_171);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_53);
lean::dec(x_55);
x_195 = lean::cnstr_get(x_181, 0);
lean::inc(x_195);
lean::dec(x_181);
if (lean::is_scalar(x_103)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_198, 0, x_195);
x_3 = x_198;
x_4 = x_183;
goto lbl_5;
}
else
{
obj* x_200; obj* x_202; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_181);
x_200 = lean::cnstr_get(x_171, 6);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_171, 7);
lean::inc(x_202);
lean::dec(x_171);
x_205 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_205, 0, x_53);
lean::cnstr_set(x_205, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_206 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_206 = x_10;
}
lean::cnstr_set(x_206, 0, x_202);
lean::cnstr_set(x_206, 1, x_205);
if (lean::is_scalar(x_15)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_15;
}
lean::cnstr_set(x_207, 0, x_200);
lean::cnstr_set(x_207, 1, x_206);
if (lean::is_scalar(x_20)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_20;
}
lean::cnstr_set(x_208, 0, x_173);
lean::cnstr_set(x_208, 1, x_207);
if (lean::is_scalar(x_25)) {
 x_209 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_209 = x_25;
}
lean::cnstr_set(x_209, 0, x_55);
lean::cnstr_set(x_209, 1, x_208);
x_210 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_210, 0, x_209);
if (lean::is_scalar(x_103)) {
 x_211 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_211 = x_103;
}
lean::cnstr_set(x_211, 0, x_210);
x_3 = x_211;
x_4 = x_183;
goto lbl_5;
}
}
}
}
else
{
obj* x_214; obj* x_215; obj* x_217; obj* x_220; 
lean::inc(x_60);
lean::inc(x_0);
x_214 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_60, x_2);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
lean::dec(x_214);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 lean::cnstr_release(x_60, 1);
 x_220 = x_60;
} else {
 lean::dec(x_60);
 x_220 = lean::box(0);
}
if (lean::obj_tag(x_215) == 0)
{
obj* x_232; obj* x_234; obj* x_235; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_220);
lean::dec(x_53);
lean::dec(x_55);
x_232 = lean::cnstr_get(x_215, 0);
if (lean::is_exclusive(x_215)) {
 x_234 = x_215;
} else {
 lean::inc(x_232);
 lean::dec(x_215);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_232);
x_3 = x_235;
x_4 = x_217;
goto lbl_5;
}
else
{
obj* x_236; obj* x_237; obj* x_239; obj* x_240; obj* x_242; 
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 x_236 = x_215;
} else {
 lean::dec(x_215);
 x_236 = lean::box(0);
}
x_237 = lean::cnstr_get(x_53, 0);
lean::inc(x_237);
x_239 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_239, 0, x_237);
x_240 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_240, 0, x_239);
lean::inc(x_21);
x_242 = l_lean_run__expander___rarg(x_240, x_21);
if (lean::obj_tag(x_242) == 0)
{
obj* x_243; obj* x_247; obj* x_248; obj* x_250; 
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
lean::dec(x_242);
lean::inc(x_0);
x_247 = lean::apply_2(x_0, x_243, x_217);
x_248 = lean::cnstr_get(x_247, 0);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_247, 1);
lean::inc(x_250);
lean::dec(x_247);
if (lean::obj_tag(x_248) == 0)
{
obj* x_264; obj* x_267; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_220);
lean::dec(x_53);
lean::dec(x_55);
x_264 = lean::cnstr_get(x_248, 0);
lean::inc(x_264);
lean::dec(x_248);
if (lean::is_scalar(x_236)) {
 x_267 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_267 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_267, 0, x_264);
x_3 = x_267;
x_4 = x_250;
goto lbl_5;
}
else
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_248);
if (lean::is_scalar(x_220)) {
 x_269 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_269 = x_220;
}
lean::cnstr_set(x_269, 0, x_53);
lean::cnstr_set(x_269, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_270 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_270 = x_10;
}
lean::cnstr_set(x_270, 0, x_21);
lean::cnstr_set(x_270, 1, x_269);
if (lean::is_scalar(x_15)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_15;
}
lean::cnstr_set(x_271, 0, x_16);
lean::cnstr_set(x_271, 1, x_270);
if (lean::is_scalar(x_20)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_20;
}
lean::cnstr_set(x_272, 0, x_11);
lean::cnstr_set(x_272, 1, x_271);
if (lean::is_scalar(x_25)) {
 x_273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_273 = x_25;
}
lean::cnstr_set(x_273, 0, x_55);
lean::cnstr_set(x_273, 1, x_272);
x_274 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
if (lean::is_scalar(x_236)) {
 x_275 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_275 = x_236;
}
lean::cnstr_set(x_275, 0, x_274);
x_3 = x_275;
x_4 = x_250;
goto lbl_5;
}
}
else
{
obj* x_278; obj* x_281; obj* x_283; 
lean::dec(x_16);
lean::dec(x_21);
x_278 = lean::cnstr_get(x_242, 0);
lean::inc(x_278);
lean::dec(x_242);
x_281 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_281, 0, x_11);
lean::inc(x_278);
x_283 = l_lean_run__elaborator___rarg(x_281, x_278);
if (lean::obj_tag(x_283) == 0)
{
obj* x_289; obj* x_292; uint8 x_293; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_55);
x_289 = lean::cnstr_get(x_283, 0);
lean::inc(x_289);
lean::dec(x_283);
x_292 = l_lean_parser_module_eoi;
x_293 = l_lean_parser_syntax_is__of__kind___main(x_292, x_278);
if (x_293 == 0)
{
obj* x_294; obj* x_295; obj* x_296; obj* x_298; 
x_294 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
x_295 = l_io_println___at_lean_run__frontend___spec__3(x_294, x_217);
x_296 = lean::cnstr_get(x_295, 0);
lean::inc(x_296);
x_298 = lean::cnstr_get(x_295, 1);
lean::inc(x_298);
lean::dec(x_295);
if (lean::obj_tag(x_296) == 0)
{
obj* x_305; obj* x_308; 
lean::dec(x_23);
lean::dec(x_220);
lean::dec(x_53);
lean::dec(x_289);
x_305 = lean::cnstr_get(x_296, 0);
lean::inc(x_305);
lean::dec(x_296);
if (lean::is_scalar(x_236)) {
 x_308 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_308 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_308, 0, x_305);
x_3 = x_308;
x_4 = x_298;
goto lbl_5;
}
else
{
obj* x_310; obj* x_312; obj* x_313; obj* x_315; 
lean::dec(x_296);
x_310 = l_list_reverse___rarg(x_289);
lean::inc(x_0);
x_312 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_310, x_298);
x_313 = lean::cnstr_get(x_312, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_312, 1);
lean::inc(x_315);
lean::dec(x_312);
if (lean::obj_tag(x_313) == 0)
{
obj* x_321; obj* x_324; 
lean::dec(x_23);
lean::dec(x_220);
lean::dec(x_53);
x_321 = lean::cnstr_get(x_313, 0);
lean::inc(x_321);
lean::dec(x_313);
if (lean::is_scalar(x_236)) {
 x_324 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_324 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_324, 0, x_321);
x_3 = x_324;
x_4 = x_315;
goto lbl_5;
}
else
{
obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
lean::dec(x_313);
if (lean::is_scalar(x_220)) {
 x_326 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_326 = x_220;
}
lean::cnstr_set(x_326, 0, x_53);
lean::cnstr_set(x_326, 1, x_23);
x_327 = l_list_reverse___rarg(x_326);
x_328 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_328, 0, x_327);
if (lean::is_scalar(x_236)) {
 x_329 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_329 = x_236;
}
lean::cnstr_set(x_329, 0, x_328);
x_3 = x_329;
x_4 = x_315;
goto lbl_5;
}
}
}
else
{
obj* x_330; obj* x_332; obj* x_333; obj* x_335; 
x_330 = l_list_reverse___rarg(x_289);
lean::inc(x_0);
x_332 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_330, x_217);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_341; obj* x_344; 
lean::dec(x_23);
lean::dec(x_220);
lean::dec(x_53);
x_341 = lean::cnstr_get(x_333, 0);
lean::inc(x_341);
lean::dec(x_333);
if (lean::is_scalar(x_236)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_344, 0, x_341);
x_3 = x_344;
x_4 = x_335;
goto lbl_5;
}
else
{
obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
lean::dec(x_333);
if (lean::is_scalar(x_220)) {
 x_346 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_346 = x_220;
}
lean::cnstr_set(x_346, 0, x_53);
lean::cnstr_set(x_346, 1, x_23);
x_347 = l_list_reverse___rarg(x_346);
x_348 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_348, 0, x_347);
if (lean::is_scalar(x_236)) {
 x_349 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_349 = x_236;
}
lean::cnstr_set(x_349, 0, x_348);
x_3 = x_349;
x_4 = x_335;
goto lbl_5;
}
}
}
else
{
obj* x_351; obj* x_353; obj* x_356; obj* x_358; obj* x_360; obj* x_361; obj* x_363; 
lean::dec(x_278);
x_351 = lean::cnstr_get(x_283, 0);
lean::inc(x_351);
x_353 = lean::cnstr_get(x_283, 1);
lean::inc(x_353);
lean::dec(x_283);
x_356 = lean::cnstr_get(x_351, 5);
lean::inc(x_356);
x_358 = l_list_reverse___rarg(x_356);
lean::inc(x_0);
x_360 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_358, x_217);
x_361 = lean::cnstr_get(x_360, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_360, 1);
lean::inc(x_363);
lean::dec(x_360);
if (lean::obj_tag(x_361) == 0)
{
obj* x_376; obj* x_379; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_220);
lean::dec(x_53);
lean::dec(x_55);
lean::dec(x_351);
lean::dec(x_353);
x_376 = lean::cnstr_get(x_361, 0);
lean::inc(x_376);
lean::dec(x_361);
if (lean::is_scalar(x_236)) {
 x_379 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_379 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_379, 0, x_376);
x_3 = x_379;
x_4 = x_363;
goto lbl_5;
}
else
{
obj* x_381; obj* x_383; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; 
lean::dec(x_361);
x_381 = lean::cnstr_get(x_351, 6);
lean::inc(x_381);
x_383 = lean::cnstr_get(x_351, 7);
lean::inc(x_383);
lean::dec(x_351);
if (lean::is_scalar(x_220)) {
 x_386 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_386 = x_220;
}
lean::cnstr_set(x_386, 0, x_53);
lean::cnstr_set(x_386, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_10;
}
lean::cnstr_set(x_387, 0, x_383);
lean::cnstr_set(x_387, 1, x_386);
if (lean::is_scalar(x_15)) {
 x_388 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_388 = x_15;
}
lean::cnstr_set(x_388, 0, x_381);
lean::cnstr_set(x_388, 1, x_387);
if (lean::is_scalar(x_20)) {
 x_389 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_389 = x_20;
}
lean::cnstr_set(x_389, 0, x_353);
lean::cnstr_set(x_389, 1, x_388);
if (lean::is_scalar(x_25)) {
 x_390 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_390 = x_25;
}
lean::cnstr_set(x_390, 0, x_55);
lean::cnstr_set(x_390, 1, x_389);
x_391 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_391, 0, x_390);
if (lean::is_scalar(x_236)) {
 x_392 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_392 = x_236;
}
lean::cnstr_set(x_392, 0, x_391);
x_3 = x_392;
x_4 = x_363;
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
obj* x_394; obj* x_396; obj* x_397; obj* x_398; 
lean::dec(x_0);
x_394 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_396 = x_3;
} else {
 lean::inc(x_394);
 lean::dec(x_3);
 x_396 = lean::box(0);
}
if (lean::is_scalar(x_396)) {
 x_397 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_397 = x_396;
}
lean::cnstr_set(x_397, 0, x_394);
x_398 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_398, 0, x_397);
lean::cnstr_set(x_398, 1, x_4);
return x_398;
}
else
{
obj* x_399; obj* x_401; 
x_399 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_401 = x_3;
} else {
 lean::inc(x_399);
 lean::dec(x_3);
 x_401 = lean::box(0);
}
if (lean::obj_tag(x_399) == 0)
{
obj* x_403; 
lean::dec(x_401);
x_403 = lean::cnstr_get(x_399, 0);
lean::inc(x_403);
lean::dec(x_399);
x_1 = x_403;
x_2 = x_4;
goto _start;
}
else
{
obj* x_408; obj* x_411; obj* x_412; 
lean::dec(x_0);
x_408 = lean::cnstr_get(x_399, 0);
lean::inc(x_408);
lean::dec(x_399);
if (lean::is_scalar(x_401)) {
 x_411 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_411 = x_401;
}
lean::cnstr_set(x_411, 0, x_408);
x_412 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_412, 0, x_411);
lean::cnstr_set(x_412, 1, x_4);
return x_412;
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
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_4 = lean::box(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file___lambda__1___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
lean::inc(x_0);
x_7 = l_lean_run__frontend(x_0, x_1, x_5, x_3);
x_8 = lean::cnstr_get(x_7, 0);
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_12 = x_7;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
if (x_2 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; 
lean::dec(x_12);
x_19 = lean::box(0);
x_20 = l_lean_elaborator_notation_elaborate___closed__1;
x_21 = 2;
x_22 = l_string_join___closed__1;
x_23 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_19);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set(x_23, 4, x_13);
lean::cnstr_set_scalar(x_23, sizeof(void*)*5, x_21);
x_24 = x_23;
x_25 = l_lean_message_to__string(x_24);
x_26 = l_io_println___at_lean_run__frontend___spec__3(x_25, x_10);
x_27 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_29 = x_26;
} else {
 lean::inc(x_27);
 lean::dec(x_26);
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
obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; uint8 x_46; obj* x_47; obj* x_48; 
lean::dec(x_16);
x_36 = l_string_quote(x_13);
x_37 = l_lean_process__file___closed__1;
x_38 = lean::string_append(x_37, x_36);
lean::dec(x_36);
x_40 = l_lean_process__file___lambda__1___closed__7;
x_41 = lean::string_append(x_38, x_40);
x_42 = l_io_println___at_lean_run__frontend___spec__3(x_41, x_10);
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
x_46 = 0;
x_47 = lean::box(x_46);
if (lean::is_scalar(x_12)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_12;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_43);
return x_48;
}
}
else
{
uint8 x_51; obj* x_52; obj* x_53; 
lean::dec(x_8);
lean::dec(x_0);
x_51 = 1;
x_52 = lean::box(x_51);
if (lean::is_scalar(x_12)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_12;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_10);
return x_53;
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

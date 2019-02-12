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
obj* l_lean_process__file___closed__2;
extern obj* l_lean_parser_module_eoi;
obj* l_lean_elaborator_run(obj*);
extern obj* l_lean_message__log_empty;
obj* l_lean_run__parser(obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_reader__t_run___rarg(obj*, obj*);
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
obj* l___private_init_io_10__put__str___at_lean_run__frontend___spec__5(obj*, obj*);
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
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_2 = l_lean_parser_module_tokens;
lean::inc(x_2);
x_4 = l_lean_parser_tokens___rarg(x_2);
x_5 = l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
lean::inc(x_5);
x_7 = l_lean_parser_tokens___rarg(x_5);
x_8 = l_list_append___rarg(x_4, x_7);
x_9 = l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
lean::inc(x_9);
x_11 = l_lean_parser_tokens___rarg(x_9);
x_12 = l_list_append___rarg(x_8, x_11);
x_13 = l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
lean::inc(x_13);
x_15 = l_lean_parser_tokens___rarg(x_13);
x_16 = l_list_append___rarg(x_12, x_15);
x_17 = l_lean_parser_mk__token__trie(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_22 = x_17;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_37; obj* x_38; obj* x_40; obj* x_41; 
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_26 = x_17;
}
lean::inc(x_1);
x_28 = l_lean_file__map_from__string(x_1);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_1);
lean::cnstr_set(x_29, 2, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_24);
x_31 = lean::box(0);
x_32 = l_lean_parser_term_builtin__leading__parsers;
x_33 = l_lean_parser_term_builtin__trailing__parsers;
lean::inc(x_31);
lean::inc(x_33);
lean::inc(x_32);
x_37 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_37, 0, x_30);
lean::cnstr_set(x_37, 1, x_32);
lean::cnstr_set(x_37, 2, x_33);
lean::cnstr_set(x_37, 3, x_31);
lean::cnstr_set(x_37, 4, x_31);
x_38 = l_lean_parser_command_builtin__command__parsers;
lean::inc(x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_37);
lean::cnstr_set(x_40, 1, x_38);
if (lean::is_scalar(x_26)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_26;
}
lean::cnstr_set(x_41, 0, x_40);
return x_41;
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
obj* x_5; obj* x_6; obj* x_7; obj* x_9; 
lean::dec(x_2);
x_5 = lean::string_mk_iterator(x_1);
x_6 = lean::apply_2(x_0, x_5, x_3);
x_7 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_6);
lean::closure_set(x_9, 1, x_7);
return x_9;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_5 = x_0;
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
obj* l_lean_parser_run___at_lean_run__frontend___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_3 = l_lean_message__log_empty;
lean::inc(x_0);
lean::inc(x_3);
x_6 = lean::apply_2(x_2, x_3, x_0);
x_7 = l_string_join___closed__1;
x_8 = l_lean_parser_run___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_7);
x_11 = l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(x_6, x_1, x_7, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1), 2, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_4 = x_1;
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
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
lean::inc(x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_22);
if (lean::is_scalar(x_4)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_4;
}
lean::cnstr_set(x_25, 0, x_11);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_28; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_0);
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_31);
if (lean::is_scalar(x_4)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_4;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_33);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* l_io_prim_lift__eio___at_lean_run__frontend___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
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
lean::inc(x_13);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_15 = x_3;
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
obj* l___private_init_io_10__put__str___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1) {
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
x_2 = l___private_init_io_10__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_lean_run__frontend___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_2 = l___private_init_io_10__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_7 = x_2;
}
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
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
obj* x_15; obj* x_17; 
lean::dec(x_7);
lean::dec(x_3);
x_15 = l_lean_format_be___main___closed__1;
lean::inc(x_15);
x_17 = l___private_init_io_10__put__str___at_lean_run__frontend___spec__5(x_15, x_5);
return x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_8, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_0);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_1 = x_10;
x_2 = x_17;
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
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_10 = x_1;
}
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_15 = x_8;
}
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_20 = x_13;
}
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_25 = x_18;
}
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_26, 0, x_6);
lean::inc(x_16);
x_28 = l_lean_run__parser___rarg(x_26, x_16);
if (lean::obj_tag(x_28) == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_28);
x_37 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
lean::inc(x_37);
x_39 = l_io_println___at_lean_run__frontend___spec__3(x_37, x_2);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_23);
x_46 = lean::cnstr_get(x_40, 0);
lean::inc(x_46);
if (lean::is_shared(x_40)) {
 lean::dec(x_40);
 x_48 = lean::box(0);
} else {
 lean::cnstr_release(x_40, 0);
 x_48 = x_40;
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
x_3 = x_49;
x_4 = x_42;
goto lbl_5;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
if (lean::is_shared(x_40)) {
 lean::dec(x_40);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_40, 0);
 x_50 = x_40;
}
x_51 = l_list_reverse___rarg(x_23);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
x_3 = x_53;
x_4 = x_42;
goto lbl_5;
}
}
else
{
obj* x_54; obj* x_56; obj* x_59; obj* x_61; 
x_54 = lean::cnstr_get(x_28, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_28, 1);
lean::inc(x_56);
lean::dec(x_28);
x_59 = lean::cnstr_get(x_54, 1);
lean::inc(x_59);
x_61 = l_list_reverse___rarg(x_59);
if (lean::obj_tag(x_61) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_68; 
lean::dec(x_61);
x_63 = lean::cnstr_get(x_54, 0);
lean::inc(x_63);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_65, 0, x_63);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_66, 0, x_65);
lean::inc(x_21);
x_68 = l_lean_run__expander___rarg(x_66, x_21);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_71 = x_68;
}
lean::inc(x_0);
x_73 = lean::apply_2(x_0, x_69, x_2);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_89; obj* x_92; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_54);
lean::dec(x_56);
x_89 = lean::cnstr_get(x_74, 0);
lean::inc(x_89);
lean::dec(x_74);
if (lean::is_scalar(x_71)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_71;
}
lean::cnstr_set(x_92, 0, x_89);
x_3 = x_92;
x_4 = x_76;
goto lbl_5;
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_74);
x_94 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_94, 0, x_54);
lean::cnstr_set(x_94, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_10;
}
lean::cnstr_set(x_95, 0, x_21);
lean::cnstr_set(x_95, 1, x_94);
if (lean::is_scalar(x_15)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_15;
}
lean::cnstr_set(x_96, 0, x_16);
lean::cnstr_set(x_96, 1, x_95);
if (lean::is_scalar(x_20)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_20;
}
lean::cnstr_set(x_97, 0, x_11);
lean::cnstr_set(x_97, 1, x_96);
if (lean::is_scalar(x_25)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_25;
}
lean::cnstr_set(x_98, 0, x_56);
lean::cnstr_set(x_98, 1, x_97);
x_99 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_99, 0, x_98);
if (lean::is_scalar(x_71)) {
 x_100 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_100 = x_71;
 lean::cnstr_set_tag(x_71, 1);
}
lean::cnstr_set(x_100, 0, x_99);
x_3 = x_100;
x_4 = x_76;
goto lbl_5;
}
}
else
{
obj* x_103; obj* x_105; obj* x_106; obj* x_108; 
lean::dec(x_16);
lean::dec(x_21);
x_103 = lean::cnstr_get(x_68, 0);
lean::inc(x_103);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_105 = x_68;
}
x_106 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_106, 0, x_11);
lean::inc(x_103);
x_108 = l_lean_run__elaborator___rarg(x_106, x_103);
if (lean::obj_tag(x_108) == 0)
{
obj* x_114; obj* x_117; uint8 x_119; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_56);
x_114 = lean::cnstr_get(x_108, 0);
lean::inc(x_114);
lean::dec(x_108);
x_117 = l_lean_parser_module_eoi;
lean::inc(x_117);
x_119 = l_lean_parser_syntax_is__of__kind___main(x_117, x_103);
if (x_119 == 0)
{
obj* x_120; obj* x_122; obj* x_123; obj* x_125; 
x_120 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_120);
x_122 = l_io_println___at_lean_run__frontend___spec__3(x_120, x_2);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
lean::dec(x_122);
if (lean::obj_tag(x_123) == 0)
{
obj* x_131; obj* x_134; 
lean::dec(x_23);
lean::dec(x_114);
lean::dec(x_54);
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
if (lean::is_scalar(x_105)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_105;
 lean::cnstr_set_tag(x_105, 0);
}
lean::cnstr_set(x_134, 0, x_131);
x_3 = x_134;
x_4 = x_125;
goto lbl_5;
}
else
{
obj* x_136; obj* x_138; obj* x_139; obj* x_141; 
lean::dec(x_123);
x_136 = l_list_reverse___rarg(x_114);
lean::inc(x_0);
x_138 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_136, x_125);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
lean::dec(x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_146; obj* x_149; 
lean::dec(x_23);
lean::dec(x_54);
x_146 = lean::cnstr_get(x_139, 0);
lean::inc(x_146);
lean::dec(x_139);
if (lean::is_scalar(x_105)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_105;
 lean::cnstr_set_tag(x_105, 0);
}
lean::cnstr_set(x_149, 0, x_146);
x_3 = x_149;
x_4 = x_141;
goto lbl_5;
}
else
{
obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_139);
x_151 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_151, 0, x_54);
lean::cnstr_set(x_151, 1, x_23);
x_152 = l_list_reverse___rarg(x_151);
x_153 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_153, 0, x_152);
if (lean::is_scalar(x_105)) {
 x_154 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_154 = x_105;
}
lean::cnstr_set(x_154, 0, x_153);
x_3 = x_154;
x_4 = x_141;
goto lbl_5;
}
}
}
else
{
obj* x_155; obj* x_157; obj* x_158; obj* x_160; 
x_155 = l_list_reverse___rarg(x_114);
lean::inc(x_0);
x_157 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_155, x_2);
x_158 = lean::cnstr_get(x_157, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_157, 1);
lean::inc(x_160);
lean::dec(x_157);
if (lean::obj_tag(x_158) == 0)
{
obj* x_165; obj* x_168; 
lean::dec(x_23);
lean::dec(x_54);
x_165 = lean::cnstr_get(x_158, 0);
lean::inc(x_165);
lean::dec(x_158);
if (lean::is_scalar(x_105)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_105;
 lean::cnstr_set_tag(x_105, 0);
}
lean::cnstr_set(x_168, 0, x_165);
x_3 = x_168;
x_4 = x_160;
goto lbl_5;
}
else
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
lean::dec(x_158);
x_170 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_170, 0, x_54);
lean::cnstr_set(x_170, 1, x_23);
x_171 = l_list_reverse___rarg(x_170);
x_172 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_172, 0, x_171);
if (lean::is_scalar(x_105)) {
 x_173 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_173 = x_105;
}
lean::cnstr_set(x_173, 0, x_172);
x_3 = x_173;
x_4 = x_160;
goto lbl_5;
}
}
}
else
{
obj* x_175; obj* x_177; obj* x_180; obj* x_182; obj* x_184; obj* x_185; obj* x_187; 
lean::dec(x_103);
x_175 = lean::cnstr_get(x_108, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_108, 1);
lean::inc(x_177);
lean::dec(x_108);
x_180 = lean::cnstr_get(x_175, 5);
lean::inc(x_180);
x_182 = l_list_reverse___rarg(x_180);
lean::inc(x_0);
x_184 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_182, x_2);
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
lean::dec(x_184);
if (lean::obj_tag(x_185) == 0)
{
obj* x_199; obj* x_202; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_54);
lean::dec(x_56);
lean::dec(x_177);
lean::dec(x_175);
x_199 = lean::cnstr_get(x_185, 0);
lean::inc(x_199);
lean::dec(x_185);
if (lean::is_scalar(x_105)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_105;
 lean::cnstr_set_tag(x_105, 0);
}
lean::cnstr_set(x_202, 0, x_199);
x_3 = x_202;
x_4 = x_187;
goto lbl_5;
}
else
{
obj* x_204; obj* x_206; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_185);
x_204 = lean::cnstr_get(x_175, 6);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_175, 7);
lean::inc(x_206);
lean::dec(x_175);
x_209 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_209, 0, x_54);
lean::cnstr_set(x_209, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_10;
}
lean::cnstr_set(x_210, 0, x_206);
lean::cnstr_set(x_210, 1, x_209);
if (lean::is_scalar(x_15)) {
 x_211 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_211 = x_15;
}
lean::cnstr_set(x_211, 0, x_204);
lean::cnstr_set(x_211, 1, x_210);
if (lean::is_scalar(x_20)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_20;
}
lean::cnstr_set(x_212, 0, x_177);
lean::cnstr_set(x_212, 1, x_211);
if (lean::is_scalar(x_25)) {
 x_213 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_213 = x_25;
}
lean::cnstr_set(x_213, 0, x_56);
lean::cnstr_set(x_213, 1, x_212);
x_214 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_214, 0, x_213);
if (lean::is_scalar(x_105)) {
 x_215 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_215 = x_105;
}
lean::cnstr_set(x_215, 0, x_214);
x_3 = x_215;
x_4 = x_187;
goto lbl_5;
}
}
}
}
else
{
obj* x_217; obj* x_218; obj* x_220; 
lean::inc(x_0);
x_217 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_61, x_2);
x_218 = lean::cnstr_get(x_217, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_217, 1);
lean::inc(x_220);
lean::dec(x_217);
if (lean::obj_tag(x_218) == 0)
{
obj* x_233; obj* x_235; obj* x_236; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_54);
lean::dec(x_56);
x_233 = lean::cnstr_get(x_218, 0);
lean::inc(x_233);
if (lean::is_shared(x_218)) {
 lean::dec(x_218);
 x_235 = lean::box(0);
} else {
 lean::cnstr_release(x_218, 0);
 x_235 = x_218;
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
x_3 = x_236;
x_4 = x_220;
goto lbl_5;
}
else
{
obj* x_237; obj* x_238; obj* x_240; obj* x_241; obj* x_243; 
if (lean::is_shared(x_218)) {
 lean::dec(x_218);
 x_237 = lean::box(0);
} else {
 lean::cnstr_release(x_218, 0);
 x_237 = x_218;
}
x_238 = lean::cnstr_get(x_54, 0);
lean::inc(x_238);
x_240 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_240, 0, x_238);
x_241 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_241, 0, x_240);
lean::inc(x_21);
x_243 = l_lean_run__expander___rarg(x_241, x_21);
if (lean::obj_tag(x_243) == 0)
{
obj* x_244; obj* x_248; obj* x_249; obj* x_251; 
x_244 = lean::cnstr_get(x_243, 0);
lean::inc(x_244);
lean::dec(x_243);
lean::inc(x_0);
x_248 = lean::apply_2(x_0, x_244, x_220);
x_249 = lean::cnstr_get(x_248, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_248, 1);
lean::inc(x_251);
lean::dec(x_248);
if (lean::obj_tag(x_249) == 0)
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
lean::dec(x_54);
lean::dec(x_56);
x_264 = lean::cnstr_get(x_249, 0);
lean::inc(x_264);
lean::dec(x_249);
if (lean::is_scalar(x_237)) {
 x_267 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_267 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_267, 0, x_264);
x_3 = x_267;
x_4 = x_251;
goto lbl_5;
}
else
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_249);
x_269 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_269, 0, x_54);
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
lean::cnstr_set(x_273, 0, x_56);
lean::cnstr_set(x_273, 1, x_272);
x_274 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
if (lean::is_scalar(x_237)) {
 x_275 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_275 = x_237;
}
lean::cnstr_set(x_275, 0, x_274);
x_3 = x_275;
x_4 = x_251;
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
obj* x_289; obj* x_292; uint8 x_294; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_56);
x_289 = lean::cnstr_get(x_283, 0);
lean::inc(x_289);
lean::dec(x_283);
x_292 = l_lean_parser_module_eoi;
lean::inc(x_292);
x_294 = l_lean_parser_syntax_is__of__kind___main(x_292, x_278);
if (x_294 == 0)
{
obj* x_295; obj* x_297; obj* x_298; obj* x_300; 
x_295 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_295);
x_297 = l_io_println___at_lean_run__frontend___spec__3(x_295, x_220);
x_298 = lean::cnstr_get(x_297, 0);
lean::inc(x_298);
x_300 = lean::cnstr_get(x_297, 1);
lean::inc(x_300);
lean::dec(x_297);
if (lean::obj_tag(x_298) == 0)
{
obj* x_306; obj* x_309; 
lean::dec(x_289);
lean::dec(x_23);
lean::dec(x_54);
x_306 = lean::cnstr_get(x_298, 0);
lean::inc(x_306);
lean::dec(x_298);
if (lean::is_scalar(x_237)) {
 x_309 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_309 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_309, 0, x_306);
x_3 = x_309;
x_4 = x_300;
goto lbl_5;
}
else
{
obj* x_311; obj* x_313; obj* x_314; obj* x_316; 
lean::dec(x_298);
x_311 = l_list_reverse___rarg(x_289);
lean::inc(x_0);
x_313 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_311, x_300);
x_314 = lean::cnstr_get(x_313, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_313, 1);
lean::inc(x_316);
lean::dec(x_313);
if (lean::obj_tag(x_314) == 0)
{
obj* x_321; obj* x_324; 
lean::dec(x_23);
lean::dec(x_54);
x_321 = lean::cnstr_get(x_314, 0);
lean::inc(x_321);
lean::dec(x_314);
if (lean::is_scalar(x_237)) {
 x_324 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_324 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_324, 0, x_321);
x_3 = x_324;
x_4 = x_316;
goto lbl_5;
}
else
{
obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
lean::dec(x_314);
x_326 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_326, 0, x_54);
lean::cnstr_set(x_326, 1, x_23);
x_327 = l_list_reverse___rarg(x_326);
x_328 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_328, 0, x_327);
if (lean::is_scalar(x_237)) {
 x_329 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_329 = x_237;
}
lean::cnstr_set(x_329, 0, x_328);
x_3 = x_329;
x_4 = x_316;
goto lbl_5;
}
}
}
else
{
obj* x_330; obj* x_332; obj* x_333; obj* x_335; 
x_330 = l_list_reverse___rarg(x_289);
lean::inc(x_0);
x_332 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_330, x_220);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_340; obj* x_343; 
lean::dec(x_23);
lean::dec(x_54);
x_340 = lean::cnstr_get(x_333, 0);
lean::inc(x_340);
lean::dec(x_333);
if (lean::is_scalar(x_237)) {
 x_343 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_343 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_343, 0, x_340);
x_3 = x_343;
x_4 = x_335;
goto lbl_5;
}
else
{
obj* x_345; obj* x_346; obj* x_347; obj* x_348; 
lean::dec(x_333);
x_345 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_345, 0, x_54);
lean::cnstr_set(x_345, 1, x_23);
x_346 = l_list_reverse___rarg(x_345);
x_347 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_347, 0, x_346);
if (lean::is_scalar(x_237)) {
 x_348 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_348 = x_237;
}
lean::cnstr_set(x_348, 0, x_347);
x_3 = x_348;
x_4 = x_335;
goto lbl_5;
}
}
}
else
{
obj* x_350; obj* x_352; obj* x_355; obj* x_357; obj* x_359; obj* x_360; obj* x_362; 
lean::dec(x_278);
x_350 = lean::cnstr_get(x_283, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_283, 1);
lean::inc(x_352);
lean::dec(x_283);
x_355 = lean::cnstr_get(x_350, 5);
lean::inc(x_355);
x_357 = l_list_reverse___rarg(x_355);
lean::inc(x_0);
x_359 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_357, x_220);
x_360 = lean::cnstr_get(x_359, 0);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_359, 1);
lean::inc(x_362);
lean::dec(x_359);
if (lean::obj_tag(x_360) == 0)
{
obj* x_374; obj* x_377; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_352);
lean::dec(x_350);
lean::dec(x_54);
lean::dec(x_56);
x_374 = lean::cnstr_get(x_360, 0);
lean::inc(x_374);
lean::dec(x_360);
if (lean::is_scalar(x_237)) {
 x_377 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_377 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_377, 0, x_374);
x_3 = x_377;
x_4 = x_362;
goto lbl_5;
}
else
{
obj* x_379; obj* x_381; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; 
lean::dec(x_360);
x_379 = lean::cnstr_get(x_350, 6);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_350, 7);
lean::inc(x_381);
lean::dec(x_350);
x_384 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_384, 0, x_54);
lean::cnstr_set(x_384, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_385 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_385 = x_10;
}
lean::cnstr_set(x_385, 0, x_381);
lean::cnstr_set(x_385, 1, x_384);
if (lean::is_scalar(x_15)) {
 x_386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_386 = x_15;
}
lean::cnstr_set(x_386, 0, x_379);
lean::cnstr_set(x_386, 1, x_385);
if (lean::is_scalar(x_20)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_20;
}
lean::cnstr_set(x_387, 0, x_352);
lean::cnstr_set(x_387, 1, x_386);
if (lean::is_scalar(x_25)) {
 x_388 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_388 = x_25;
}
lean::cnstr_set(x_388, 0, x_56);
lean::cnstr_set(x_388, 1, x_387);
x_389 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_389, 0, x_388);
if (lean::is_scalar(x_237)) {
 x_390 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_390 = x_237;
}
lean::cnstr_set(x_390, 0, x_389);
x_3 = x_390;
x_4 = x_362;
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
obj* x_392; obj* x_394; obj* x_395; obj* x_396; 
lean::dec(x_0);
x_392 = lean::cnstr_get(x_3, 0);
lean::inc(x_392);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_394 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_394 = x_3;
}
if (lean::is_scalar(x_394)) {
 x_395 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_395 = x_394;
}
lean::cnstr_set(x_395, 0, x_392);
x_396 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_396, 0, x_395);
lean::cnstr_set(x_396, 1, x_4);
return x_396;
}
else
{
obj* x_397; obj* x_399; 
x_397 = lean::cnstr_get(x_3, 0);
lean::inc(x_397);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_399 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_399 = x_3;
}
if (lean::obj_tag(x_397) == 0)
{
obj* x_401; 
lean::dec(x_399);
x_401 = lean::cnstr_get(x_397, 0);
lean::inc(x_401);
lean::dec(x_397);
x_1 = x_401;
x_2 = x_4;
goto _start;
}
else
{
obj* x_406; obj* x_409; obj* x_410; 
lean::dec(x_0);
x_406 = lean::cnstr_get(x_397, 0);
lean::inc(x_406);
lean::dec(x_397);
if (lean::is_scalar(x_399)) {
 x_409 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_409 = x_399;
}
lean::cnstr_set(x_409, 0, x_406);
x_410 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_410, 0, x_409);
lean::cnstr_set(x_410, 1, x_4);
return x_410;
}
}
}
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
obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::inc(x_1);
x_6 = l_lean_file__map_from__string(x_1);
lean::inc(x_1);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_1);
lean::cnstr_set(x_8, 2, x_6);
x_9 = l_lean_expander_builtin__transformers;
lean::inc(x_9);
lean::inc(x_8);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_9);
x_13 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1;
lean::inc(x_13);
lean::inc(x_4);
x_16 = l_lean_parser_run___at_lean_run__frontend___spec__1(x_4, x_1, x_13);
lean::inc(x_4);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_4);
x_19 = l_lean_elaborator_run(x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_4);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15(x_2, x_24, x_3);
return x_25;
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
lean::inc(x_10);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_12 = x_9;
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
lean::inc(x_14);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_16 = x_9;
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
lean::inc(x_21);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_23 = x_4;
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
obj* _init_l_lean_process__file___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
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
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
if (x_2 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; 
lean::dec(x_12);
x_19 = lean::box(0);
x_20 = l_lean_elaborator_notation_elaborate___closed__1;
x_21 = 2;
x_22 = l_string_join___closed__1;
lean::inc(x_22);
lean::inc(x_20);
x_25 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_20);
lean::cnstr_set(x_25, 2, x_19);
lean::cnstr_set(x_25, 3, x_22);
lean::cnstr_set(x_25, 4, x_13);
lean::cnstr_set_scalar(x_25, sizeof(void*)*5, x_21);
x_26 = x_25;
x_27 = l_lean_message_to__string(x_26);
x_28 = l_io_println___at_lean_run__frontend___spec__3(x_27, x_10);
x_29 = lean::cnstr_get(x_28, 1);
lean::inc(x_29);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 x_31 = x_28;
}
x_32 = 0;
x_33 = lean::box(x_32);
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
obj* x_36; 
lean::dec(x_0);
x_36 = lean::box(0);
x_16 = x_36;
goto lbl_17;
}
lbl_17:
{
obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_49; obj* x_50; obj* x_51; 
lean::dec(x_16);
x_38 = l_string_quote(x_13);
x_39 = l_lean_process__file___closed__1;
lean::inc(x_39);
x_41 = lean::string_append(x_39, x_38);
lean::dec(x_38);
x_43 = l_lean_process__file___closed__2;
x_44 = lean::string_append(x_41, x_43);
x_45 = l_io_println___at_lean_run__frontend___spec__3(x_44, x_10);
x_46 = lean::cnstr_get(x_45, 1);
lean::inc(x_46);
lean::dec(x_45);
x_49 = 0;
x_50 = lean::box(x_49);
if (lean::is_scalar(x_12)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_12;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_46);
return x_51;
}
}
else
{
uint8 x_54; obj* x_55; obj* x_56; 
lean::dec(x_8);
lean::dec(x_0);
x_54 = 1;
x_55 = lean::box(x_54);
if (lean::is_scalar(x_12)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_12;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_10);
return x_56;
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
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("warning");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* _init_l_lean_process__file___lambda__1___closed__8() {
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
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_35; 
lean::dec(x_3);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
x_13 = l_nat_repr(x_11);
x_14 = l_lean_process__file___lambda__1___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_13);
lean::dec(x_13);
x_18 = l_lean_process__file___lambda__1___closed__2;
x_19 = lean::string_append(x_16, x_18);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
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
x_46 = l_lean_process__file___closed__2;
x_47 = lean::string_append(x_44, x_46);
x_48 = l_io_println___at_lean_run__frontend___spec__3(x_47, x_2);
return x_48;
}
case 1:
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
x_49 = l_lean_process__file___lambda__1___closed__7;
x_50 = lean::string_append(x_27, x_49);
x_51 = l_lean_process__file___lambda__1___closed__5;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::string_append(x_52, x_31);
lean::dec(x_31);
x_55 = l_lean_process__file___lambda__1___closed__6;
x_56 = lean::string_append(x_53, x_55);
x_57 = lean::string_append(x_56, x_35);
lean::dec(x_35);
x_59 = l_lean_process__file___closed__2;
x_60 = lean::string_append(x_57, x_59);
x_61 = l_io_println___at_lean_run__frontend___spec__3(x_60, x_2);
return x_61;
}
default:
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
x_62 = l_lean_process__file___lambda__1___closed__8;
x_63 = lean::string_append(x_27, x_62);
x_64 = l_lean_process__file___lambda__1___closed__5;
x_65 = lean::string_append(x_63, x_64);
x_66 = lean::string_append(x_65, x_31);
lean::dec(x_31);
x_68 = l_lean_process__file___lambda__1___closed__6;
x_69 = lean::string_append(x_66, x_68);
x_70 = lean::string_append(x_69, x_35);
lean::dec(x_35);
x_72 = l_lean_process__file___closed__2;
x_73 = lean::string_append(x_70, x_72);
x_74 = l_io_println___at_lean_run__frontend___spec__3(x_73, x_2);
return x_74;
}
}
}
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
obj* l_lean_process__file___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_process__file___lambda__1(x_3, x_1, x_2);
return x_4;
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
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2();
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1();
 l_lean_process__file___closed__1 = _init_l_lean_process__file___closed__1();
 l_lean_process__file___closed__2 = _init_l_lean_process__file___closed__2();
 l_lean_process__file___lambda__1___closed__1 = _init_l_lean_process__file___lambda__1___closed__1();
 l_lean_process__file___lambda__1___closed__2 = _init_l_lean_process__file___lambda__1___closed__2();
 l_lean_process__file___lambda__1___closed__3 = _init_l_lean_process__file___lambda__1___closed__3();
 l_lean_process__file___lambda__1___closed__4 = _init_l_lean_process__file___lambda__1___closed__4();
 l_lean_process__file___lambda__1___closed__5 = _init_l_lean_process__file___lambda__1___closed__5();
 l_lean_process__file___lambda__1___closed__6 = _init_l_lean_process__file___lambda__1___closed__6();
 l_lean_process__file___lambda__1___closed__7 = _init_l_lean_process__file___lambda__1___closed__7();
 l_lean_process__file___lambda__1___closed__8 = _init_l_lean_process__file___lambda__1___closed__8();
}

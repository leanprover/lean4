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
obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_40; 
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
lean::inc(x_33);
lean::inc(x_32);
x_36 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_36, 0, x_30);
lean::cnstr_set(x_36, 1, x_32);
lean::cnstr_set(x_36, 2, x_33);
lean::cnstr_set(x_36, 3, x_31);
lean::cnstr_set(x_36, 4, x_31);
x_37 = l_lean_parser_command_builtin__command__parsers;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
if (lean::is_scalar(x_26)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_26;
}
lean::cnstr_set(x_40, 0, x_39);
return x_40;
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
x_17 = l___private_init_io_12__put__str___at_lean_run__frontend___spec__5(x_15, x_5);
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_2(x_0, x_7, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_16;
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
obj* x_62; obj* x_64; obj* x_65; obj* x_67; 
x_62 = lean::cnstr_get(x_54, 0);
lean::inc(x_62);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_64, 0, x_62);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_65, 0, x_64);
lean::inc(x_21);
x_67 = l_lean_run__expander___rarg(x_65, x_21);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; 
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_70 = x_67;
}
lean::inc(x_0);
x_72 = lean::apply_2(x_0, x_68, x_2);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_88; obj* x_91; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_54);
x_88 = lean::cnstr_get(x_73, 0);
lean::inc(x_88);
lean::dec(x_73);
if (lean::is_scalar(x_70)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_70;
}
lean::cnstr_set(x_91, 0, x_88);
x_3 = x_91;
x_4 = x_75;
goto lbl_5;
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_73);
x_93 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_93, 0, x_54);
lean::cnstr_set(x_93, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_10;
}
lean::cnstr_set(x_94, 0, x_21);
lean::cnstr_set(x_94, 1, x_93);
if (lean::is_scalar(x_15)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_15;
}
lean::cnstr_set(x_95, 0, x_16);
lean::cnstr_set(x_95, 1, x_94);
if (lean::is_scalar(x_20)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_20;
}
lean::cnstr_set(x_96, 0, x_11);
lean::cnstr_set(x_96, 1, x_95);
if (lean::is_scalar(x_25)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_25;
}
lean::cnstr_set(x_97, 0, x_56);
lean::cnstr_set(x_97, 1, x_96);
x_98 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_98, 0, x_97);
if (lean::is_scalar(x_70)) {
 x_99 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_99 = x_70;
 lean::cnstr_set_tag(x_70, 1);
}
lean::cnstr_set(x_99, 0, x_98);
x_3 = x_99;
x_4 = x_75;
goto lbl_5;
}
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_16);
lean::dec(x_21);
x_102 = lean::cnstr_get(x_67, 0);
lean::inc(x_102);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_104 = x_67;
}
x_105 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_105, 0, x_11);
lean::inc(x_102);
x_107 = l_lean_run__elaborator___rarg(x_105, x_102);
if (lean::obj_tag(x_107) == 0)
{
obj* x_113; obj* x_116; uint8 x_118; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
x_113 = lean::cnstr_get(x_107, 0);
lean::inc(x_113);
lean::dec(x_107);
x_116 = l_lean_parser_module_eoi;
lean::inc(x_116);
x_118 = l_lean_parser_syntax_is__of__kind___main(x_116, x_102);
if (x_118 == 0)
{
obj* x_119; obj* x_121; obj* x_122; obj* x_124; 
x_119 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_119);
x_121 = l_io_println___at_lean_run__frontend___spec__3(x_119, x_2);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_130; obj* x_133; 
lean::dec(x_23);
lean::dec(x_54);
lean::dec(x_113);
x_130 = lean::cnstr_get(x_122, 0);
lean::inc(x_130);
lean::dec(x_122);
if (lean::is_scalar(x_104)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_133, 0, x_130);
x_3 = x_133;
x_4 = x_124;
goto lbl_5;
}
else
{
obj* x_135; obj* x_137; obj* x_138; obj* x_140; 
lean::dec(x_122);
x_135 = l_list_reverse___rarg(x_113);
lean::inc(x_0);
x_137 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_135, x_124);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
lean::dec(x_137);
if (lean::obj_tag(x_138) == 0)
{
obj* x_145; obj* x_148; 
lean::dec(x_23);
lean::dec(x_54);
x_145 = lean::cnstr_get(x_138, 0);
lean::inc(x_145);
lean::dec(x_138);
if (lean::is_scalar(x_104)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_148, 0, x_145);
x_3 = x_148;
x_4 = x_140;
goto lbl_5;
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_138);
x_150 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_150, 0, x_54);
lean::cnstr_set(x_150, 1, x_23);
x_151 = l_list_reverse___rarg(x_150);
x_152 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_152, 0, x_151);
if (lean::is_scalar(x_104)) {
 x_153 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_153 = x_104;
}
lean::cnstr_set(x_153, 0, x_152);
x_3 = x_153;
x_4 = x_140;
goto lbl_5;
}
}
}
else
{
obj* x_154; obj* x_156; obj* x_157; obj* x_159; 
x_154 = l_list_reverse___rarg(x_113);
lean::inc(x_0);
x_156 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_154, x_2);
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_164; obj* x_167; 
lean::dec(x_23);
lean::dec(x_54);
x_164 = lean::cnstr_get(x_157, 0);
lean::inc(x_164);
lean::dec(x_157);
if (lean::is_scalar(x_104)) {
 x_167 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_167 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_167, 0, x_164);
x_3 = x_167;
x_4 = x_159;
goto lbl_5;
}
else
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_157);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_54);
lean::cnstr_set(x_169, 1, x_23);
x_170 = l_list_reverse___rarg(x_169);
x_171 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_171, 0, x_170);
if (lean::is_scalar(x_104)) {
 x_172 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_172 = x_104;
}
lean::cnstr_set(x_172, 0, x_171);
x_3 = x_172;
x_4 = x_159;
goto lbl_5;
}
}
}
else
{
obj* x_174; obj* x_176; obj* x_179; obj* x_181; obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_102);
x_174 = lean::cnstr_get(x_107, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_107, 1);
lean::inc(x_176);
lean::dec(x_107);
x_179 = lean::cnstr_get(x_174, 5);
lean::inc(x_179);
x_181 = l_list_reverse___rarg(x_179);
lean::inc(x_0);
x_183 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_181, x_2);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_198; obj* x_201; 
lean::dec(x_174);
lean::dec(x_176);
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_54);
x_198 = lean::cnstr_get(x_184, 0);
lean::inc(x_198);
lean::dec(x_184);
if (lean::is_scalar(x_104)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_201, 0, x_198);
x_3 = x_201;
x_4 = x_186;
goto lbl_5;
}
else
{
obj* x_203; obj* x_205; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; 
lean::dec(x_184);
x_203 = lean::cnstr_get(x_174, 6);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_174, 7);
lean::inc(x_205);
lean::dec(x_174);
x_208 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_208, 0, x_54);
lean::cnstr_set(x_208, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_209 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_209 = x_10;
}
lean::cnstr_set(x_209, 0, x_205);
lean::cnstr_set(x_209, 1, x_208);
if (lean::is_scalar(x_15)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_15;
}
lean::cnstr_set(x_210, 0, x_203);
lean::cnstr_set(x_210, 1, x_209);
if (lean::is_scalar(x_20)) {
 x_211 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_211 = x_20;
}
lean::cnstr_set(x_211, 0, x_176);
lean::cnstr_set(x_211, 1, x_210);
if (lean::is_scalar(x_25)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_25;
}
lean::cnstr_set(x_212, 0, x_56);
lean::cnstr_set(x_212, 1, x_211);
x_213 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_213, 0, x_212);
if (lean::is_scalar(x_104)) {
 x_214 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_214 = x_104;
}
lean::cnstr_set(x_214, 0, x_213);
x_3 = x_214;
x_4 = x_186;
goto lbl_5;
}
}
}
}
else
{
obj* x_216; obj* x_217; obj* x_219; 
lean::inc(x_0);
x_216 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_61, x_2);
x_217 = lean::cnstr_get(x_216, 0);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 1);
lean::inc(x_219);
lean::dec(x_216);
if (lean::obj_tag(x_217) == 0)
{
obj* x_232; obj* x_234; obj* x_235; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_54);
x_232 = lean::cnstr_get(x_217, 0);
lean::inc(x_232);
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 x_234 = x_217;
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_232);
x_3 = x_235;
x_4 = x_219;
goto lbl_5;
}
else
{
obj* x_236; obj* x_237; obj* x_239; obj* x_240; obj* x_242; 
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_236 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 x_236 = x_217;
}
x_237 = lean::cnstr_get(x_54, 0);
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
x_247 = lean::apply_2(x_0, x_243, x_219);
x_248 = lean::cnstr_get(x_247, 0);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_247, 1);
lean::inc(x_250);
lean::dec(x_247);
if (lean::obj_tag(x_248) == 0)
{
obj* x_263; obj* x_266; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_16);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_54);
x_263 = lean::cnstr_get(x_248, 0);
lean::inc(x_263);
lean::dec(x_248);
if (lean::is_scalar(x_236)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_266, 0, x_263);
x_3 = x_266;
x_4 = x_250;
goto lbl_5;
}
else
{
obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
lean::dec(x_248);
x_268 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_268, 0, x_54);
lean::cnstr_set(x_268, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_10;
}
lean::cnstr_set(x_269, 0, x_21);
lean::cnstr_set(x_269, 1, x_268);
if (lean::is_scalar(x_15)) {
 x_270 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_270 = x_15;
}
lean::cnstr_set(x_270, 0, x_16);
lean::cnstr_set(x_270, 1, x_269);
if (lean::is_scalar(x_20)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_20;
}
lean::cnstr_set(x_271, 0, x_11);
lean::cnstr_set(x_271, 1, x_270);
if (lean::is_scalar(x_25)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_25;
}
lean::cnstr_set(x_272, 0, x_56);
lean::cnstr_set(x_272, 1, x_271);
x_273 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_273, 0, x_272);
if (lean::is_scalar(x_236)) {
 x_274 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_274 = x_236;
}
lean::cnstr_set(x_274, 0, x_273);
x_3 = x_274;
x_4 = x_250;
goto lbl_5;
}
}
else
{
obj* x_277; obj* x_280; obj* x_282; 
lean::dec(x_16);
lean::dec(x_21);
x_277 = lean::cnstr_get(x_242, 0);
lean::inc(x_277);
lean::dec(x_242);
x_280 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_280, 0, x_11);
lean::inc(x_277);
x_282 = l_lean_run__elaborator___rarg(x_280, x_277);
if (lean::obj_tag(x_282) == 0)
{
obj* x_288; obj* x_291; uint8 x_293; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
x_288 = lean::cnstr_get(x_282, 0);
lean::inc(x_288);
lean::dec(x_282);
x_291 = l_lean_parser_module_eoi;
lean::inc(x_291);
x_293 = l_lean_parser_syntax_is__of__kind___main(x_291, x_277);
if (x_293 == 0)
{
obj* x_294; obj* x_296; obj* x_297; obj* x_299; 
x_294 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_294);
x_296 = l_io_println___at_lean_run__frontend___spec__3(x_294, x_219);
x_297 = lean::cnstr_get(x_296, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_296, 1);
lean::inc(x_299);
lean::dec(x_296);
if (lean::obj_tag(x_297) == 0)
{
obj* x_305; obj* x_308; 
lean::dec(x_23);
lean::dec(x_54);
lean::dec(x_288);
x_305 = lean::cnstr_get(x_297, 0);
lean::inc(x_305);
lean::dec(x_297);
if (lean::is_scalar(x_236)) {
 x_308 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_308 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_308, 0, x_305);
x_3 = x_308;
x_4 = x_299;
goto lbl_5;
}
else
{
obj* x_310; obj* x_312; obj* x_313; obj* x_315; 
lean::dec(x_297);
x_310 = l_list_reverse___rarg(x_288);
lean::inc(x_0);
x_312 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_310, x_299);
x_313 = lean::cnstr_get(x_312, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_312, 1);
lean::inc(x_315);
lean::dec(x_312);
if (lean::obj_tag(x_313) == 0)
{
obj* x_320; obj* x_323; 
lean::dec(x_23);
lean::dec(x_54);
x_320 = lean::cnstr_get(x_313, 0);
lean::inc(x_320);
lean::dec(x_313);
if (lean::is_scalar(x_236)) {
 x_323 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_323 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_323, 0, x_320);
x_3 = x_323;
x_4 = x_315;
goto lbl_5;
}
else
{
obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
lean::dec(x_313);
x_325 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_325, 0, x_54);
lean::cnstr_set(x_325, 1, x_23);
x_326 = l_list_reverse___rarg(x_325);
x_327 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_327, 0, x_326);
if (lean::is_scalar(x_236)) {
 x_328 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_328 = x_236;
}
lean::cnstr_set(x_328, 0, x_327);
x_3 = x_328;
x_4 = x_315;
goto lbl_5;
}
}
}
else
{
obj* x_329; obj* x_331; obj* x_332; obj* x_334; 
x_329 = l_list_reverse___rarg(x_288);
lean::inc(x_0);
x_331 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_329, x_219);
x_332 = lean::cnstr_get(x_331, 0);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_331, 1);
lean::inc(x_334);
lean::dec(x_331);
if (lean::obj_tag(x_332) == 0)
{
obj* x_339; obj* x_342; 
lean::dec(x_23);
lean::dec(x_54);
x_339 = lean::cnstr_get(x_332, 0);
lean::inc(x_339);
lean::dec(x_332);
if (lean::is_scalar(x_236)) {
 x_342 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_342 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_342, 0, x_339);
x_3 = x_342;
x_4 = x_334;
goto lbl_5;
}
else
{
obj* x_344; obj* x_345; obj* x_346; obj* x_347; 
lean::dec(x_332);
x_344 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_344, 0, x_54);
lean::cnstr_set(x_344, 1, x_23);
x_345 = l_list_reverse___rarg(x_344);
x_346 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_346, 0, x_345);
if (lean::is_scalar(x_236)) {
 x_347 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_347 = x_236;
}
lean::cnstr_set(x_347, 0, x_346);
x_3 = x_347;
x_4 = x_334;
goto lbl_5;
}
}
}
else
{
obj* x_349; obj* x_351; obj* x_354; obj* x_356; obj* x_358; obj* x_359; obj* x_361; 
lean::dec(x_277);
x_349 = lean::cnstr_get(x_282, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get(x_282, 1);
lean::inc(x_351);
lean::dec(x_282);
x_354 = lean::cnstr_get(x_349, 5);
lean::inc(x_354);
x_356 = l_list_reverse___rarg(x_354);
lean::inc(x_0);
x_358 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_356, x_219);
x_359 = lean::cnstr_get(x_358, 0);
lean::inc(x_359);
x_361 = lean::cnstr_get(x_358, 1);
lean::inc(x_361);
lean::dec(x_358);
if (lean::obj_tag(x_359) == 0)
{
obj* x_373; obj* x_376; 
lean::dec(x_23);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_54);
lean::dec(x_351);
lean::dec(x_349);
x_373 = lean::cnstr_get(x_359, 0);
lean::inc(x_373);
lean::dec(x_359);
if (lean::is_scalar(x_236)) {
 x_376 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_376 = x_236;
 lean::cnstr_set_tag(x_236, 0);
}
lean::cnstr_set(x_376, 0, x_373);
x_3 = x_376;
x_4 = x_361;
goto lbl_5;
}
else
{
obj* x_378; obj* x_380; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; 
lean::dec(x_359);
x_378 = lean::cnstr_get(x_349, 6);
lean::inc(x_378);
x_380 = lean::cnstr_get(x_349, 7);
lean::inc(x_380);
lean::dec(x_349);
x_383 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_383, 0, x_54);
lean::cnstr_set(x_383, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_384 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_384 = x_10;
}
lean::cnstr_set(x_384, 0, x_380);
lean::cnstr_set(x_384, 1, x_383);
if (lean::is_scalar(x_15)) {
 x_385 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_385 = x_15;
}
lean::cnstr_set(x_385, 0, x_378);
lean::cnstr_set(x_385, 1, x_384);
if (lean::is_scalar(x_20)) {
 x_386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_386 = x_20;
}
lean::cnstr_set(x_386, 0, x_351);
lean::cnstr_set(x_386, 1, x_385);
if (lean::is_scalar(x_25)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_25;
}
lean::cnstr_set(x_387, 0, x_56);
lean::cnstr_set(x_387, 1, x_386);
x_388 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_388, 0, x_387);
if (lean::is_scalar(x_236)) {
 x_389 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_389 = x_236;
}
lean::cnstr_set(x_389, 0, x_388);
x_3 = x_389;
x_4 = x_361;
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
obj* x_391; obj* x_393; obj* x_394; obj* x_395; 
lean::dec(x_0);
x_391 = lean::cnstr_get(x_3, 0);
lean::inc(x_391);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_393 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_393 = x_3;
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_391);
x_395 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_395, 0, x_394);
lean::cnstr_set(x_395, 1, x_4);
return x_395;
}
else
{
obj* x_396; obj* x_398; 
x_396 = lean::cnstr_get(x_3, 0);
lean::inc(x_396);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_398 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_398 = x_3;
}
if (lean::obj_tag(x_396) == 0)
{
obj* x_400; 
lean::dec(x_398);
x_400 = lean::cnstr_get(x_396, 0);
lean::inc(x_400);
lean::dec(x_396);
x_1 = x_400;
x_2 = x_4;
goto _start;
}
else
{
obj* x_405; obj* x_408; obj* x_409; 
lean::dec(x_0);
x_405 = lean::cnstr_get(x_396, 0);
lean::inc(x_405);
lean::dec(x_396);
if (lean::is_scalar(x_398)) {
 x_408 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_408 = x_398;
}
lean::cnstr_set(x_408, 0, x_405);
x_409 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_409, 0, x_408);
lean::cnstr_set(x_409, 1, x_4);
return x_409;
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
x_46 = l_lean_process__file___lambda__1___closed__7;
x_47 = lean::string_append(x_44, x_46);
x_48 = l_io_println___at_lean_run__frontend___spec__3(x_47, x_2);
return x_48;
}
case 1:
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
x_49 = l_lean_process__file___lambda__1___closed__8;
x_50 = lean::string_append(x_27, x_49);
x_51 = l_lean_process__file___lambda__1___closed__5;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::string_append(x_52, x_31);
lean::dec(x_31);
x_55 = l_lean_process__file___lambda__1___closed__6;
x_56 = lean::string_append(x_53, x_55);
x_57 = lean::string_append(x_56, x_35);
lean::dec(x_35);
x_59 = l_lean_process__file___lambda__1___closed__7;
x_60 = lean::string_append(x_57, x_59);
x_61 = l_io_println___at_lean_run__frontend___spec__3(x_60, x_2);
return x_61;
}
default:
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
x_62 = l_lean_process__file___lambda__1___closed__9;
x_63 = lean::string_append(x_27, x_62);
x_64 = l_lean_process__file___lambda__1___closed__5;
x_65 = lean::string_append(x_63, x_64);
x_66 = lean::string_append(x_65, x_31);
lean::dec(x_31);
x_68 = l_lean_process__file___lambda__1___closed__6;
x_69 = lean::string_append(x_66, x_68);
x_70 = lean::string_append(x_69, x_35);
lean::dec(x_35);
x_72 = l_lean_process__file___lambda__1___closed__7;
x_73 = lean::string_append(x_70, x_72);
x_74 = l_io_println___at_lean_run__frontend___spec__3(x_73, x_2);
return x_74;
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
x_43 = l_lean_process__file___lambda__1___closed__7;
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
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2();
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1();
 l_lean_process__file___lambda__1___closed__1 = _init_l_lean_process__file___lambda__1___closed__1();
 l_lean_process__file___lambda__1___closed__2 = _init_l_lean_process__file___lambda__1___closed__2();
 l_lean_process__file___lambda__1___closed__3 = _init_l_lean_process__file___lambda__1___closed__3();
 l_lean_process__file___lambda__1___closed__4 = _init_l_lean_process__file___lambda__1___closed__4();
 l_lean_process__file___lambda__1___closed__5 = _init_l_lean_process__file___lambda__1___closed__5();
 l_lean_process__file___lambda__1___closed__6 = _init_l_lean_process__file___lambda__1___closed__6();
 l_lean_process__file___lambda__1___closed__7 = _init_l_lean_process__file___lambda__1___closed__7();
 l_lean_process__file___lambda__1___closed__8 = _init_l_lean_process__file___lambda__1___closed__8();
 l_lean_process__file___lambda__1___closed__9 = _init_l_lean_process__file___lambda__1___closed__9();
 l_lean_process__file___closed__1 = _init_l_lean_process__file___closed__1();
}

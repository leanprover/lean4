// Lean compiler output
// Module: init.lean.frontend
// Imports: init.default init.lean.parser.module init.lean.expander init.lean.elaborator init.io
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_io_prim_iterate__eio___at_lean_process__file__json___spec__5(obj*, obj*);
unsigned char l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_process__file__json___lambda__1___closed__8;
obj* l_lean_process__file__json___lambda__1___closed__6;
obj* l_coroutine_resume___rarg(obj*, obj*);
obj* l_lean_parser_module_parser(obj*, obj*, obj*);
obj* l_lean_run__parser(obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
obj* l_io_fs_handle_close___at_lean_process__file__json___spec__8(obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1;
obj* l_lean_run__expander___rarg(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj*, obj*, obj*);
obj* l_lean_run__elaborator___rarg(obj*, obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_lean_run__parser___rarg(obj*, obj*);
obj* l_lean_process__file__json___lambda__1___closed__2;
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(obj*, obj*);
obj* l_lean_run__elaborator(obj*, obj*);
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_process__file__json___lambda__1___closed__3;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj*, obj*, obj*);
obj* l_lean_process__file__json___lambda__1___closed__4;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(obj*, obj*, obj*);
obj* l_io_println___at_lean_run__frontend___spec__3(obj*, obj*);
obj* l_io_fs_read__file___at_lean_process__file__json___spec__1(obj*, unsigned char, obj*);
obj* l_lean_process__file__json___lambda__1___closed__7;
obj* l_lean_process__file__json___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*);
obj* l_io_prim_handle_mk___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_elaborator_run(obj*);
obj* l_lean_process__file__json___lambda__1___closed__9;
obj* l_lean_parser_run___at_lean_run__frontend___spec__1___lambda__1(obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_lean_process__file__json___lambda__1___closed__5;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_lean_run__frontend___closed__1;
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_reader__t_run___rarg(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_process__file__json___spec__6(obj*, obj*, obj*);
obj* l_io_fs_handle_mk___at_lean_process__file__json___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___at_lean_process__file__json___spec__3(obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(obj*, obj*, obj*);
obj* l_io_fs_handle_read__to__end___at_lean_process__file__json___spec__4(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15(obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_mk__config(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_io_fs_handle_mk___at_lean_process__file__json___spec__2(obj*, unsigned char, unsigned char, obj*);
obj* l_lean_process__file__json___lambda__1(obj*, obj*);
extern obj* l_lean_expander_builtin__transformers;
extern obj* l_lean_format_be___main___closed__1;
obj* l_list_reverse___rarg(obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_run___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
obj* l_lean_file__map_from__string(obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
obj* l_io_prim_lift__eio___at_lean_run__frontend___spec__6(obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1(obj*);
extern obj* l_lean_parser_module_tokens;
obj* l_nat_repr(obj*);
obj* l_list_append___main___rarg(obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
obj* l_io_prim_lift__eio___at_lean_process__file__json___spec__7(obj*, obj*);
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14(obj*, obj*, obj*, obj*);
obj* l_lean_process__file__json___lambda__1___closed__1;
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__3(obj*, obj*);
obj* l_io_fs_read__file___at_lean_process__file__json___spec__1___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
obj* l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2(obj*, obj*);
obj* l___private_3644302523__put__str___at_lean_run__frontend___spec__5(obj*, obj*);
extern obj* l_lean_parser_run___rarg___closed__1;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(obj*, obj*, obj*);
obj* l_lean_process__file__json(obj*, obj*);
obj* l_io_print___at_lean_run__frontend___spec__4(obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
extern obj* l_lean_message__log_empty;
obj* l_lean_run__expander(obj*, obj*);
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
x_8 = l_list_append___main___rarg(x_4, x_7);
x_9 = l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
lean::inc(x_9);
x_11 = l_lean_parser_tokens___rarg(x_9);
x_12 = l_list_append___main___rarg(x_8, x_11);
x_13 = l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
lean::inc(x_13);
x_15 = l_lean_parser_tokens___rarg(x_13);
x_16 = l_list_append___main___rarg(x_12, x_15);
x_17 = l_lean_parser_mk__token__trie(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
lean::dec(x_0);
lean::dec(x_1);
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
obj* l_lean_run__frontend(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; 
x_6 = l_lean_run__frontend___closed__1;
lean::inc(x_0);
lean::inc(x_6);
x_9 = l_lean_mk__config(x_6, x_0);
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
x_3 = x_13;
x_4 = x_2;
goto lbl_5;
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
x_3 = x_17;
x_4 = x_2;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_0);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_22 = x_3;
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_4);
return x_24;
}
else
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
lean::dec(x_3);
x_28 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__14(x_0, x_1, x_4, x_25);
return x_28;
}
}
}
}
obj* _init_l_lean_run__frontend___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("<stdin>");
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
obj* _init_l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___lambda__1), 1, 0);
return x_0;
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
obj* l___private_3644302523__put__str___at_lean_run__frontend___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_put_str), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_lean_run__frontend___spec__6(x_2, x_1);
return x_3;
}
}
obj* l_io_print___at_lean_run__frontend___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_3644302523__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_lean_run__frontend___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_7; 
x_2 = l___private_3644302523__put__str___at_lean_run__frontend___spec__5(x_0, x_1);
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
x_17 = l___private_3644302523__put__str___at_lean_run__frontend___spec__5(x_15, x_5);
return x_17;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_0);
lean::dec(x_1);
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
lean::dec(x_10);
lean::dec(x_11);
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
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_54);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_23);
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
obj* x_114; obj* x_117; unsigned char x_119; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
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
lean::dec(x_114);
lean::dec(x_54);
lean::dec(x_23);
x_131 = lean::cnstr_get(x_123, 0);
lean::inc(x_131);
lean::dec(x_123);
if (lean::is_scalar(x_105)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_105;
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
lean::dec(x_54);
lean::dec(x_23);
x_146 = lean::cnstr_get(x_139, 0);
lean::inc(x_146);
lean::dec(x_139);
if (lean::is_scalar(x_105)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_105;
}
lean::cnstr_set(x_149, 0, x_146);
x_3 = x_149;
x_4 = x_141;
goto lbl_5;
}
else
{
obj* x_151; obj* x_152; obj* x_154; obj* x_157; obj* x_158; obj* x_160; obj* x_162; obj* x_163; obj* x_164; obj* x_167; obj* x_170; obj* x_171; obj* x_173; obj* x_174; unsigned char x_175; obj* x_176; obj* x_180; obj* x_181; obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_139);
x_151 = lean::box(0);
x_152 = lean::cnstr_get(x_54, 2);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_152, 1);
lean::inc(x_154);
lean::inc(x_154);
x_157 = l_nat_repr(x_154);
x_158 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_158);
x_160 = lean::string_append(x_158, x_157);
lean::dec(x_157);
x_162 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_163 = lean::string_append(x_160, x_162);
x_164 = lean::cnstr_get(x_152, 2);
lean::inc(x_164);
lean::dec(x_152);
x_167 = lean::nat_add(x_154, x_164);
lean::dec(x_164);
lean::dec(x_154);
x_170 = l_nat_repr(x_167);
x_171 = lean::string_append(x_163, x_170);
lean::dec(x_170);
x_173 = l_lean_run__frontend___closed__1;
x_174 = l_lean_elaborator_notation_elaborate___closed__1;
x_175 = 0;
x_176 = l_string_join___closed__1;
lean::inc(x_176);
lean::inc(x_174);
lean::inc(x_173);
x_180 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_180, 0, x_173);
lean::cnstr_set(x_180, 1, x_174);
lean::cnstr_set(x_180, 2, x_151);
lean::cnstr_set(x_180, 3, x_176);
lean::cnstr_set(x_180, 4, x_171);
lean::cnstr_set_scalar(x_180, sizeof(void*)*5, x_175);
x_181 = x_180;
lean::inc(x_0);
x_183 = lean::apply_2(x_0, x_181, x_141);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_191; obj* x_194; 
lean::dec(x_54);
lean::dec(x_23);
x_191 = lean::cnstr_get(x_184, 0);
lean::inc(x_191);
lean::dec(x_184);
if (lean::is_scalar(x_105)) {
 x_194 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_194 = x_105;
}
lean::cnstr_set(x_194, 0, x_191);
x_3 = x_194;
x_4 = x_186;
goto lbl_5;
}
else
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
lean::dec(x_184);
x_196 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_196, 0, x_54);
lean::cnstr_set(x_196, 1, x_23);
x_197 = l_list_reverse___rarg(x_196);
x_198 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_198, 0, x_197);
if (lean::is_scalar(x_105)) {
 x_199 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_199 = x_105;
}
lean::cnstr_set(x_199, 0, x_198);
x_3 = x_199;
x_4 = x_186;
goto lbl_5;
}
}
}
}
else
{
obj* x_200; obj* x_202; obj* x_203; obj* x_205; 
x_200 = l_list_reverse___rarg(x_114);
lean::inc(x_0);
x_202 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_200, x_2);
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_202, 1);
lean::inc(x_205);
lean::dec(x_202);
if (lean::obj_tag(x_203) == 0)
{
obj* x_210; obj* x_213; 
lean::dec(x_54);
lean::dec(x_23);
x_210 = lean::cnstr_get(x_203, 0);
lean::inc(x_210);
lean::dec(x_203);
if (lean::is_scalar(x_105)) {
 x_213 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_213 = x_105;
}
lean::cnstr_set(x_213, 0, x_210);
x_3 = x_213;
x_4 = x_205;
goto lbl_5;
}
else
{
obj* x_215; obj* x_216; obj* x_218; obj* x_221; obj* x_222; obj* x_224; obj* x_226; obj* x_227; obj* x_228; obj* x_231; obj* x_234; obj* x_235; obj* x_237; obj* x_238; unsigned char x_239; obj* x_240; obj* x_244; obj* x_245; obj* x_247; obj* x_248; obj* x_250; 
lean::dec(x_203);
x_215 = lean::box(0);
x_216 = lean::cnstr_get(x_54, 2);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_216, 1);
lean::inc(x_218);
lean::inc(x_218);
x_221 = l_nat_repr(x_218);
x_222 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_222);
x_224 = lean::string_append(x_222, x_221);
lean::dec(x_221);
x_226 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_227 = lean::string_append(x_224, x_226);
x_228 = lean::cnstr_get(x_216, 2);
lean::inc(x_228);
lean::dec(x_216);
x_231 = lean::nat_add(x_218, x_228);
lean::dec(x_228);
lean::dec(x_218);
x_234 = l_nat_repr(x_231);
x_235 = lean::string_append(x_227, x_234);
lean::dec(x_234);
x_237 = l_lean_run__frontend___closed__1;
x_238 = l_lean_elaborator_notation_elaborate___closed__1;
x_239 = 0;
x_240 = l_string_join___closed__1;
lean::inc(x_240);
lean::inc(x_238);
lean::inc(x_237);
x_244 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_244, 0, x_237);
lean::cnstr_set(x_244, 1, x_238);
lean::cnstr_set(x_244, 2, x_215);
lean::cnstr_set(x_244, 3, x_240);
lean::cnstr_set(x_244, 4, x_235);
lean::cnstr_set_scalar(x_244, sizeof(void*)*5, x_239);
x_245 = x_244;
lean::inc(x_0);
x_247 = lean::apply_2(x_0, x_245, x_205);
x_248 = lean::cnstr_get(x_247, 0);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_247, 1);
lean::inc(x_250);
lean::dec(x_247);
if (lean::obj_tag(x_248) == 0)
{
obj* x_255; obj* x_258; 
lean::dec(x_54);
lean::dec(x_23);
x_255 = lean::cnstr_get(x_248, 0);
lean::inc(x_255);
lean::dec(x_248);
if (lean::is_scalar(x_105)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_105;
}
lean::cnstr_set(x_258, 0, x_255);
x_3 = x_258;
x_4 = x_250;
goto lbl_5;
}
else
{
obj* x_260; obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_248);
x_260 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_260, 0, x_54);
lean::cnstr_set(x_260, 1, x_23);
x_261 = l_list_reverse___rarg(x_260);
x_262 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_262, 0, x_261);
if (lean::is_scalar(x_105)) {
 x_263 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_263 = x_105;
}
lean::cnstr_set(x_263, 0, x_262);
x_3 = x_263;
x_4 = x_250;
goto lbl_5;
}
}
}
}
else
{
obj* x_265; obj* x_267; obj* x_270; obj* x_272; obj* x_274; obj* x_275; obj* x_277; 
lean::dec(x_103);
x_265 = lean::cnstr_get(x_108, 0);
lean::inc(x_265);
x_267 = lean::cnstr_get(x_108, 1);
lean::inc(x_267);
lean::dec(x_108);
x_270 = lean::cnstr_get(x_265, 5);
lean::inc(x_270);
x_272 = l_list_reverse___rarg(x_270);
lean::inc(x_0);
x_274 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_272, x_2);
x_275 = lean::cnstr_get(x_274, 0);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 1);
lean::inc(x_277);
lean::dec(x_274);
if (lean::obj_tag(x_275) == 0)
{
obj* x_289; obj* x_292; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_54);
lean::dec(x_56);
lean::dec(x_267);
lean::dec(x_265);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_23);
x_289 = lean::cnstr_get(x_275, 0);
lean::inc(x_289);
lean::dec(x_275);
if (lean::is_scalar(x_105)) {
 x_292 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_292 = x_105;
}
lean::cnstr_set(x_292, 0, x_289);
x_3 = x_292;
x_4 = x_277;
goto lbl_5;
}
else
{
obj* x_294; obj* x_296; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_275);
x_294 = lean::cnstr_get(x_265, 6);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_265, 7);
lean::inc(x_296);
lean::dec(x_265);
x_299 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_299, 0, x_54);
lean::cnstr_set(x_299, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_300 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_300 = x_10;
}
lean::cnstr_set(x_300, 0, x_296);
lean::cnstr_set(x_300, 1, x_299);
if (lean::is_scalar(x_15)) {
 x_301 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_301 = x_15;
}
lean::cnstr_set(x_301, 0, x_294);
lean::cnstr_set(x_301, 1, x_300);
if (lean::is_scalar(x_20)) {
 x_302 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_302 = x_20;
}
lean::cnstr_set(x_302, 0, x_267);
lean::cnstr_set(x_302, 1, x_301);
if (lean::is_scalar(x_25)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_25;
}
lean::cnstr_set(x_303, 0, x_56);
lean::cnstr_set(x_303, 1, x_302);
x_304 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_304, 0, x_303);
if (lean::is_scalar(x_105)) {
 x_305 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_305 = x_105;
}
lean::cnstr_set(x_305, 0, x_304);
x_3 = x_305;
x_4 = x_277;
goto lbl_5;
}
}
}
}
else
{
obj* x_307; obj* x_308; obj* x_310; 
lean::inc(x_0);
x_307 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_61, x_2);
x_308 = lean::cnstr_get(x_307, 0);
lean::inc(x_308);
x_310 = lean::cnstr_get(x_307, 1);
lean::inc(x_310);
lean::dec(x_307);
if (lean::obj_tag(x_308) == 0)
{
obj* x_323; obj* x_325; obj* x_326; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_54);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_23);
x_323 = lean::cnstr_get(x_308, 0);
lean::inc(x_323);
if (lean::is_shared(x_308)) {
 lean::dec(x_308);
 x_325 = lean::box(0);
} else {
 lean::cnstr_release(x_308, 0);
 x_325 = x_308;
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_323);
x_3 = x_326;
x_4 = x_310;
goto lbl_5;
}
else
{
obj* x_327; obj* x_328; obj* x_330; obj* x_331; obj* x_333; 
if (lean::is_shared(x_308)) {
 lean::dec(x_308);
 x_327 = lean::box(0);
} else {
 lean::cnstr_release(x_308, 0);
 x_327 = x_308;
}
x_328 = lean::cnstr_get(x_54, 0);
lean::inc(x_328);
x_330 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_330, 0, x_328);
x_331 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_331, 0, x_330);
lean::inc(x_21);
x_333 = l_lean_run__expander___rarg(x_331, x_21);
if (lean::obj_tag(x_333) == 0)
{
obj* x_334; obj* x_338; obj* x_339; obj* x_341; 
x_334 = lean::cnstr_get(x_333, 0);
lean::inc(x_334);
lean::dec(x_333);
lean::inc(x_0);
x_338 = lean::apply_2(x_0, x_334, x_310);
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
lean::dec(x_338);
if (lean::obj_tag(x_339) == 0)
{
obj* x_354; obj* x_357; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_54);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_23);
x_354 = lean::cnstr_get(x_339, 0);
lean::inc(x_354);
lean::dec(x_339);
if (lean::is_scalar(x_327)) {
 x_357 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_357 = x_327;
}
lean::cnstr_set(x_357, 0, x_354);
x_3 = x_357;
x_4 = x_341;
goto lbl_5;
}
else
{
obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; 
lean::dec(x_339);
x_359 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_359, 0, x_54);
lean::cnstr_set(x_359, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_360 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_360 = x_10;
}
lean::cnstr_set(x_360, 0, x_21);
lean::cnstr_set(x_360, 1, x_359);
if (lean::is_scalar(x_15)) {
 x_361 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_361 = x_15;
}
lean::cnstr_set(x_361, 0, x_16);
lean::cnstr_set(x_361, 1, x_360);
if (lean::is_scalar(x_20)) {
 x_362 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_362 = x_20;
}
lean::cnstr_set(x_362, 0, x_11);
lean::cnstr_set(x_362, 1, x_361);
if (lean::is_scalar(x_25)) {
 x_363 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_363 = x_25;
}
lean::cnstr_set(x_363, 0, x_56);
lean::cnstr_set(x_363, 1, x_362);
x_364 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_364, 0, x_363);
if (lean::is_scalar(x_327)) {
 x_365 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_365 = x_327;
}
lean::cnstr_set(x_365, 0, x_364);
x_3 = x_365;
x_4 = x_341;
goto lbl_5;
}
}
else
{
obj* x_368; obj* x_371; obj* x_373; 
lean::dec(x_16);
lean::dec(x_21);
x_368 = lean::cnstr_get(x_333, 0);
lean::inc(x_368);
lean::dec(x_333);
x_371 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_371, 0, x_11);
lean::inc(x_368);
x_373 = l_lean_run__elaborator___rarg(x_371, x_368);
if (lean::obj_tag(x_373) == 0)
{
obj* x_379; obj* x_382; unsigned char x_384; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
x_379 = lean::cnstr_get(x_373, 0);
lean::inc(x_379);
lean::dec(x_373);
x_382 = l_lean_parser_module_eoi;
lean::inc(x_382);
x_384 = l_lean_parser_syntax_is__of__kind___main(x_382, x_368);
if (x_384 == 0)
{
obj* x_385; obj* x_387; obj* x_388; obj* x_390; 
x_385 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_385);
x_387 = l_io_println___at_lean_run__frontend___spec__3(x_385, x_310);
x_388 = lean::cnstr_get(x_387, 0);
lean::inc(x_388);
x_390 = lean::cnstr_get(x_387, 1);
lean::inc(x_390);
lean::dec(x_387);
if (lean::obj_tag(x_388) == 0)
{
obj* x_396; obj* x_399; 
lean::dec(x_54);
lean::dec(x_23);
lean::dec(x_379);
x_396 = lean::cnstr_get(x_388, 0);
lean::inc(x_396);
lean::dec(x_388);
if (lean::is_scalar(x_327)) {
 x_399 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_399 = x_327;
}
lean::cnstr_set(x_399, 0, x_396);
x_3 = x_399;
x_4 = x_390;
goto lbl_5;
}
else
{
obj* x_401; obj* x_403; obj* x_404; obj* x_406; 
lean::dec(x_388);
x_401 = l_list_reverse___rarg(x_379);
lean::inc(x_0);
x_403 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_401, x_390);
x_404 = lean::cnstr_get(x_403, 0);
lean::inc(x_404);
x_406 = lean::cnstr_get(x_403, 1);
lean::inc(x_406);
lean::dec(x_403);
if (lean::obj_tag(x_404) == 0)
{
obj* x_411; obj* x_414; 
lean::dec(x_54);
lean::dec(x_23);
x_411 = lean::cnstr_get(x_404, 0);
lean::inc(x_411);
lean::dec(x_404);
if (lean::is_scalar(x_327)) {
 x_414 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_414 = x_327;
}
lean::cnstr_set(x_414, 0, x_411);
x_3 = x_414;
x_4 = x_406;
goto lbl_5;
}
else
{
obj* x_416; obj* x_417; obj* x_419; obj* x_422; obj* x_423; obj* x_425; obj* x_427; obj* x_428; obj* x_429; obj* x_432; obj* x_435; obj* x_436; obj* x_438; obj* x_439; unsigned char x_440; obj* x_441; obj* x_445; obj* x_446; obj* x_448; obj* x_449; obj* x_451; 
lean::dec(x_404);
x_416 = lean::box(0);
x_417 = lean::cnstr_get(x_54, 2);
lean::inc(x_417);
x_419 = lean::cnstr_get(x_417, 1);
lean::inc(x_419);
lean::inc(x_419);
x_422 = l_nat_repr(x_419);
x_423 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_423);
x_425 = lean::string_append(x_423, x_422);
lean::dec(x_422);
x_427 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_428 = lean::string_append(x_425, x_427);
x_429 = lean::cnstr_get(x_417, 2);
lean::inc(x_429);
lean::dec(x_417);
x_432 = lean::nat_add(x_419, x_429);
lean::dec(x_429);
lean::dec(x_419);
x_435 = l_nat_repr(x_432);
x_436 = lean::string_append(x_428, x_435);
lean::dec(x_435);
x_438 = l_lean_run__frontend___closed__1;
x_439 = l_lean_elaborator_notation_elaborate___closed__1;
x_440 = 0;
x_441 = l_string_join___closed__1;
lean::inc(x_441);
lean::inc(x_439);
lean::inc(x_438);
x_445 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_445, 0, x_438);
lean::cnstr_set(x_445, 1, x_439);
lean::cnstr_set(x_445, 2, x_416);
lean::cnstr_set(x_445, 3, x_441);
lean::cnstr_set(x_445, 4, x_436);
lean::cnstr_set_scalar(x_445, sizeof(void*)*5, x_440);
x_446 = x_445;
lean::inc(x_0);
x_448 = lean::apply_2(x_0, x_446, x_406);
x_449 = lean::cnstr_get(x_448, 0);
lean::inc(x_449);
x_451 = lean::cnstr_get(x_448, 1);
lean::inc(x_451);
lean::dec(x_448);
if (lean::obj_tag(x_449) == 0)
{
obj* x_456; obj* x_459; 
lean::dec(x_54);
lean::dec(x_23);
x_456 = lean::cnstr_get(x_449, 0);
lean::inc(x_456);
lean::dec(x_449);
if (lean::is_scalar(x_327)) {
 x_459 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_459 = x_327;
}
lean::cnstr_set(x_459, 0, x_456);
x_3 = x_459;
x_4 = x_451;
goto lbl_5;
}
else
{
obj* x_461; obj* x_462; obj* x_463; obj* x_464; 
lean::dec(x_449);
x_461 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_461, 0, x_54);
lean::cnstr_set(x_461, 1, x_23);
x_462 = l_list_reverse___rarg(x_461);
x_463 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_463, 0, x_462);
if (lean::is_scalar(x_327)) {
 x_464 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_464 = x_327;
}
lean::cnstr_set(x_464, 0, x_463);
x_3 = x_464;
x_4 = x_451;
goto lbl_5;
}
}
}
}
else
{
obj* x_465; obj* x_467; obj* x_468; obj* x_470; 
x_465 = l_list_reverse___rarg(x_379);
lean::inc(x_0);
x_467 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_465, x_310);
x_468 = lean::cnstr_get(x_467, 0);
lean::inc(x_468);
x_470 = lean::cnstr_get(x_467, 1);
lean::inc(x_470);
lean::dec(x_467);
if (lean::obj_tag(x_468) == 0)
{
obj* x_475; obj* x_478; 
lean::dec(x_54);
lean::dec(x_23);
x_475 = lean::cnstr_get(x_468, 0);
lean::inc(x_475);
lean::dec(x_468);
if (lean::is_scalar(x_327)) {
 x_478 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_478 = x_327;
}
lean::cnstr_set(x_478, 0, x_475);
x_3 = x_478;
x_4 = x_470;
goto lbl_5;
}
else
{
obj* x_480; obj* x_481; obj* x_483; obj* x_486; obj* x_487; obj* x_489; obj* x_491; obj* x_492; obj* x_493; obj* x_496; obj* x_499; obj* x_500; obj* x_502; obj* x_503; unsigned char x_504; obj* x_505; obj* x_509; obj* x_510; obj* x_512; obj* x_513; obj* x_515; 
lean::dec(x_468);
x_480 = lean::box(0);
x_481 = lean::cnstr_get(x_54, 2);
lean::inc(x_481);
x_483 = lean::cnstr_get(x_481, 1);
lean::inc(x_483);
lean::inc(x_483);
x_486 = l_nat_repr(x_483);
x_487 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_487);
x_489 = lean::string_append(x_487, x_486);
lean::dec(x_486);
x_491 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_492 = lean::string_append(x_489, x_491);
x_493 = lean::cnstr_get(x_481, 2);
lean::inc(x_493);
lean::dec(x_481);
x_496 = lean::nat_add(x_483, x_493);
lean::dec(x_493);
lean::dec(x_483);
x_499 = l_nat_repr(x_496);
x_500 = lean::string_append(x_492, x_499);
lean::dec(x_499);
x_502 = l_lean_run__frontend___closed__1;
x_503 = l_lean_elaborator_notation_elaborate___closed__1;
x_504 = 0;
x_505 = l_string_join___closed__1;
lean::inc(x_505);
lean::inc(x_503);
lean::inc(x_502);
x_509 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_509, 0, x_502);
lean::cnstr_set(x_509, 1, x_503);
lean::cnstr_set(x_509, 2, x_480);
lean::cnstr_set(x_509, 3, x_505);
lean::cnstr_set(x_509, 4, x_500);
lean::cnstr_set_scalar(x_509, sizeof(void*)*5, x_504);
x_510 = x_509;
lean::inc(x_0);
x_512 = lean::apply_2(x_0, x_510, x_470);
x_513 = lean::cnstr_get(x_512, 0);
lean::inc(x_513);
x_515 = lean::cnstr_get(x_512, 1);
lean::inc(x_515);
lean::dec(x_512);
if (lean::obj_tag(x_513) == 0)
{
obj* x_520; obj* x_523; 
lean::dec(x_54);
lean::dec(x_23);
x_520 = lean::cnstr_get(x_513, 0);
lean::inc(x_520);
lean::dec(x_513);
if (lean::is_scalar(x_327)) {
 x_523 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_523 = x_327;
}
lean::cnstr_set(x_523, 0, x_520);
x_3 = x_523;
x_4 = x_515;
goto lbl_5;
}
else
{
obj* x_525; obj* x_526; obj* x_527; obj* x_528; 
lean::dec(x_513);
x_525 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_525, 0, x_54);
lean::cnstr_set(x_525, 1, x_23);
x_526 = l_list_reverse___rarg(x_525);
x_527 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_527, 0, x_526);
if (lean::is_scalar(x_327)) {
 x_528 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_528 = x_327;
}
lean::cnstr_set(x_528, 0, x_527);
x_3 = x_528;
x_4 = x_515;
goto lbl_5;
}
}
}
}
else
{
obj* x_530; obj* x_532; obj* x_535; obj* x_537; obj* x_539; obj* x_540; obj* x_542; 
lean::dec(x_368);
x_530 = lean::cnstr_get(x_373, 0);
lean::inc(x_530);
x_532 = lean::cnstr_get(x_373, 1);
lean::inc(x_532);
lean::dec(x_373);
x_535 = lean::cnstr_get(x_530, 5);
lean::inc(x_535);
x_537 = l_list_reverse___rarg(x_535);
lean::inc(x_0);
x_539 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_537, x_310);
x_540 = lean::cnstr_get(x_539, 0);
lean::inc(x_540);
x_542 = lean::cnstr_get(x_539, 1);
lean::inc(x_542);
lean::dec(x_539);
if (lean::obj_tag(x_540) == 0)
{
obj* x_554; obj* x_557; 
lean::dec(x_532);
lean::dec(x_530);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_54);
lean::dec(x_56);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_23);
x_554 = lean::cnstr_get(x_540, 0);
lean::inc(x_554);
lean::dec(x_540);
if (lean::is_scalar(x_327)) {
 x_557 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_557 = x_327;
}
lean::cnstr_set(x_557, 0, x_554);
x_3 = x_557;
x_4 = x_542;
goto lbl_5;
}
else
{
obj* x_559; obj* x_561; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; 
lean::dec(x_540);
x_559 = lean::cnstr_get(x_530, 6);
lean::inc(x_559);
x_561 = lean::cnstr_get(x_530, 7);
lean::inc(x_561);
lean::dec(x_530);
x_564 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_564, 0, x_54);
lean::cnstr_set(x_564, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_565 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_565 = x_10;
}
lean::cnstr_set(x_565, 0, x_561);
lean::cnstr_set(x_565, 1, x_564);
if (lean::is_scalar(x_15)) {
 x_566 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_566 = x_15;
}
lean::cnstr_set(x_566, 0, x_559);
lean::cnstr_set(x_566, 1, x_565);
if (lean::is_scalar(x_20)) {
 x_567 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_567 = x_20;
}
lean::cnstr_set(x_567, 0, x_532);
lean::cnstr_set(x_567, 1, x_566);
if (lean::is_scalar(x_25)) {
 x_568 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_568 = x_25;
}
lean::cnstr_set(x_568, 0, x_56);
lean::cnstr_set(x_568, 1, x_567);
x_569 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_569, 0, x_568);
if (lean::is_scalar(x_327)) {
 x_570 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_570 = x_327;
}
lean::cnstr_set(x_570, 0, x_569);
x_3 = x_570;
x_4 = x_542;
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
obj* x_572; obj* x_574; obj* x_575; obj* x_576; 
lean::dec(x_0);
x_572 = lean::cnstr_get(x_3, 0);
lean::inc(x_572);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_574 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_574 = x_3;
}
if (lean::is_scalar(x_574)) {
 x_575 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_575 = x_574;
}
lean::cnstr_set(x_575, 0, x_572);
x_576 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_576, 0, x_575);
lean::cnstr_set(x_576, 1, x_4);
return x_576;
}
else
{
obj* x_577; obj* x_579; 
x_577 = lean::cnstr_get(x_3, 0);
lean::inc(x_577);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_579 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_579 = x_3;
}
if (lean::obj_tag(x_577) == 0)
{
obj* x_581; 
lean::dec(x_579);
x_581 = lean::cnstr_get(x_577, 0);
lean::inc(x_581);
lean::dec(x_577);
x_1 = x_581;
x_2 = x_4;
goto _start;
}
else
{
obj* x_586; obj* x_589; obj* x_590; 
lean::dec(x_0);
x_586 = lean::cnstr_get(x_577, 0);
lean::inc(x_586);
lean::dec(x_577);
if (lean::is_scalar(x_579)) {
 x_589 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_589 = x_579;
}
lean::cnstr_set(x_589, 0, x_586);
x_590 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_590, 0, x_589);
lean::cnstr_set(x_590, 1, x_4);
return x_590;
}
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
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parser cache hit rate: ");
return x_0;
}
}
obj* _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/");
return x_0;
}
}
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::inc(x_0);
x_5 = l_lean_file__map_from__string(x_0);
x_6 = l_lean_run__frontend___closed__1;
lean::inc(x_0);
lean::inc(x_6);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_5);
x_10 = l_lean_expander_builtin__transformers;
lean::inc(x_10);
lean::inc(x_9);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_10);
x_14 = l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1;
lean::inc(x_14);
lean::inc(x_3);
x_17 = l_lean_parser_run___at_lean_run__frontend___spec__1(x_3, x_0, x_14);
lean::inc(x_3);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_3);
x_20 = l_lean_elaborator_run(x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_13);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_3);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_17);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15(x_1, x_25, x_2);
return x_26;
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
obj* l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_lean_parser_module_parser(x_0, x_2, x_3);
return x_5;
}
}
obj* l_lean_process__file__json(obj* x_0, obj* x_1) {
_start:
{
unsigned char x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
x_2 = 0;
x_3 = l_io_fs_read__file___at_lean_process__file__json___spec__1(x_0, x_2, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_8 = x_3;
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_16 = x_4;
}
x_17 = l_lean_process__file__json___closed__1;
lean::inc(x_17);
x_19 = l_lean_run__frontend(x_14, x_17, x_6);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_8)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_8;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
return x_29;
}
else
{
obj* x_32; obj* x_34; 
lean::dec(x_16);
lean::dec(x_20);
x_32 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1;
lean::inc(x_32);
if (lean::is_scalar(x_8)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_8;
}
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_22);
return x_34;
}
}
}
}
obj* _init_l_lean_process__file__json___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_process__file__json___lambda__1), 2, 0);
return x_0;
}
}
obj* l_lean_process__file__json___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; unsigned char x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_28; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = l_nat_repr(x_4);
x_7 = l_lean_process__file__json___lambda__1___closed__1;
lean::inc(x_7);
x_9 = lean::string_append(x_7, x_6);
lean::dec(x_6);
x_11 = l_lean_process__file__json___lambda__1___closed__2;
x_12 = lean::string_append(x_9, x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_16 = l_nat_repr(x_13);
x_17 = lean::string_append(x_12, x_16);
lean::dec(x_16);
x_19 = l_lean_process__file__json___lambda__1___closed__3;
x_20 = lean::string_append(x_17, x_19);
x_21 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*5);
x_22 = lean::cnstr_get(x_0, 3);
lean::inc(x_22);
x_24 = l_string_quote(x_22);
x_25 = lean::cnstr_get(x_0, 4);
lean::inc(x_25);
lean::dec(x_0);
x_28 = l_string_quote(x_25);
switch (x_21) {
case 0:
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; 
x_29 = l_lean_process__file__json___lambda__1___closed__4;
x_30 = lean::string_append(x_20, x_29);
x_31 = l_lean_process__file__json___lambda__1___closed__5;
x_32 = lean::string_append(x_30, x_31);
x_33 = lean::string_append(x_32, x_24);
lean::dec(x_24);
x_35 = l_lean_process__file__json___lambda__1___closed__6;
x_36 = lean::string_append(x_33, x_35);
x_37 = lean::string_append(x_36, x_28);
lean::dec(x_28);
x_39 = l_lean_process__file__json___lambda__1___closed__7;
x_40 = lean::string_append(x_37, x_39);
x_41 = l_io_println___at_lean_run__frontend___spec__3(x_40, x_1);
return x_41;
}
case 1:
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; 
x_42 = l_lean_process__file__json___lambda__1___closed__8;
x_43 = lean::string_append(x_20, x_42);
x_44 = l_lean_process__file__json___lambda__1___closed__5;
x_45 = lean::string_append(x_43, x_44);
x_46 = lean::string_append(x_45, x_24);
lean::dec(x_24);
x_48 = l_lean_process__file__json___lambda__1___closed__6;
x_49 = lean::string_append(x_46, x_48);
x_50 = lean::string_append(x_49, x_28);
lean::dec(x_28);
x_52 = l_lean_process__file__json___lambda__1___closed__7;
x_53 = lean::string_append(x_50, x_52);
x_54 = l_io_println___at_lean_run__frontend___spec__3(x_53, x_1);
return x_54;
}
default:
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
x_55 = l_lean_process__file__json___lambda__1___closed__9;
x_56 = lean::string_append(x_20, x_55);
x_57 = l_lean_process__file__json___lambda__1___closed__5;
x_58 = lean::string_append(x_56, x_57);
x_59 = lean::string_append(x_58, x_24);
lean::dec(x_24);
x_61 = l_lean_process__file__json___lambda__1___closed__6;
x_62 = lean::string_append(x_59, x_61);
x_63 = lean::string_append(x_62, x_28);
lean::dec(x_28);
x_65 = l_lean_process__file__json___lambda__1___closed__7;
x_66 = lean::string_append(x_63, x_65);
x_67 = l_io_println___at_lean_run__frontend___spec__3(x_66, x_1);
return x_67;
}
}
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("{\"file_name\": \"<stdin>\", \"pos_line\": ");
return x_0;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"pos_col\": ");
return x_0;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"severity\": ");
return x_0;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("information");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"caption\": ");
return x_0;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(", \"text\": ");
return x_0;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("warning");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* _init_l_lean_process__file__json___lambda__1___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("error");
x_1 = l_string_quote(x_0);
return x_1;
}
}
obj* l_io_prim_lift__eio___at_lean_process__file__json___spec__3(obj* x_0, obj* x_1) {
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
obj* l_io_fs_handle_mk___at_lean_process__file__json___spec__2(obj* x_0, unsigned char x_1, unsigned char x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(x_1);
x_5 = lean::box(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_mk___boxed), 4, 3);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_5);
x_7 = l_io_prim_lift__eio___at_lean_process__file__json___spec__3(x_6, x_3);
return x_7;
}
}
obj* l_io_prim_iterate___main___at_lean_process__file__json___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
lean::inc(x_0);
x_7 = l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(x_0, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_16 = x_8;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
x_3 = x_17;
x_4 = x_10;
goto lbl_5;
}
else
{
obj* x_18; obj* x_20; unsigned char x_21; 
x_18 = lean::cnstr_get(x_8, 0);
lean::inc(x_18);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_20 = x_8;
}
x_21 = lean::unbox(x_18);
lean::dec(x_18);
if (x_21 == 0)
{
obj* x_24; obj* x_25; obj* x_27; 
lean::inc(x_0);
x_24 = l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__3(x_0, x_10);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_34; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_20)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_20;
}
lean::cnstr_set(x_34, 0, x_31);
x_3 = x_34;
x_4 = x_27;
goto lbl_5;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_25, 0);
lean::inc(x_35);
lean::dec(x_25);
x_38 = lean::string_append(x_1, x_35);
lean::dec(x_35);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_38);
if (lean::is_scalar(x_20)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_20;
}
lean::cnstr_set(x_41, 0, x_40);
x_3 = x_41;
x_4 = x_27;
goto lbl_5;
}
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_1);
if (lean::is_scalar(x_20)) {
 x_43 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_43 = x_20;
}
lean::cnstr_set(x_43, 0, x_42);
x_3 = x_43;
x_4 = x_10;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_0);
x_45 = lean::cnstr_get(x_3, 0);
lean::inc(x_45);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_47 = x_3;
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_4);
return x_49;
}
else
{
obj* x_50; obj* x_52; 
x_50 = lean::cnstr_get(x_3, 0);
lean::inc(x_50);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_52 = x_3;
}
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; 
lean::dec(x_52);
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
lean::dec(x_50);
x_1 = x_54;
x_2 = x_4;
goto _start;
}
else
{
obj* x_59; obj* x_62; obj* x_63; 
lean::dec(x_0);
x_59 = lean::cnstr_get(x_50, 0);
lean::inc(x_59);
lean::dec(x_50);
if (lean::is_scalar(x_52)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_52;
}
lean::cnstr_set(x_62, 0, x_59);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_4);
return x_63;
}
}
}
}
}
obj* l_io_prim_iterate__eio___at_lean_process__file__json___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_string_join___closed__1;
lean::inc(x_2);
x_4 = l_io_prim_iterate___main___at_lean_process__file__json___spec__6(x_0, x_2, x_1);
return x_4;
}
}
obj* l_io_prim_lift__eio___at_lean_process__file__json___spec__7(obj* x_0, obj* x_1) {
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
obj* l_io_fs_handle_read__to__end___at_lean_process__file__json___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_lean_process__file__json___spec__5), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_lean_process__file__json___spec__7(x_2, x_1);
return x_3;
}
}
obj* l_io_fs_handle_close___at_lean_process__file__json___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(lean::io_prim_handle_flush), 2, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_io_prim_lift__eio___at_lean_run__frontend___spec__6(x_2, x_1);
return x_3;
}
}
obj* l_io_fs_read__file___at_lean_process__file__json___spec__1(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_3 = 0;
x_4 = l_io_fs_handle_mk___at_lean_process__file__json___spec__2(x_0, x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
x_15 = lean::cnstr_get(x_5, 0);
lean::inc(x_15);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_17 = x_5;
}
lean::inc(x_15);
x_19 = l_io_fs_handle_read__to__end___at_lean_process__file__json___spec__4(x_15, x_7);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; obj* x_29; obj* x_30; 
lean::dec(x_15);
x_26 = lean::cnstr_get(x_20, 0);
lean::inc(x_26);
lean::dec(x_20);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_26);
if (lean::is_scalar(x_9)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_9;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_35; obj* x_37; 
x_31 = lean::cnstr_get(x_20, 0);
lean::inc(x_31);
lean::dec(x_20);
x_34 = l_io_fs_handle_close___at_lean_process__file__json___spec__8(x_15, x_22);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_41; obj* x_44; obj* x_45; 
lean::dec(x_31);
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
if (lean::is_scalar(x_17)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_17;
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_9)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_9;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_37);
return x_45;
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_35);
if (lean::is_scalar(x_17)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_17;
}
lean::cnstr_set(x_47, 0, x_31);
if (lean::is_scalar(x_9)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_9;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_37);
return x_48;
}
}
}
}
}
obj* l_io_fs_handle_mk___at_lean_process__file__json___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; unsigned char x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = l_io_fs_handle_mk___at_lean_process__file__json___spec__2(x_0, x_4, x_5, x_3);
return x_6;
}
}
obj* l_io_fs_read__file___at_lean_process__file__json___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l_io_fs_read__file___at_lean_process__file__json___spec__1(x_0, x_3, x_2);
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
 l_lean_run__frontend___closed__1 = _init_l_lean_run__frontend___closed__1();
 l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1 = _init_l_lean_parser_parsec__t_run___at_lean_run__frontend___spec__2___rarg___closed__1();
 l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend___spec__7___closed__1();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3();
 l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4 = _init_l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4();
 l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1 = _init_l_io_prim_iterate__eio___at_lean_run__frontend___spec__14___closed__1();
 l_lean_process__file__json___closed__1 = _init_l_lean_process__file__json___closed__1();
 l_lean_process__file__json___lambda__1___closed__1 = _init_l_lean_process__file__json___lambda__1___closed__1();
 l_lean_process__file__json___lambda__1___closed__2 = _init_l_lean_process__file__json___lambda__1___closed__2();
 l_lean_process__file__json___lambda__1___closed__3 = _init_l_lean_process__file__json___lambda__1___closed__3();
 l_lean_process__file__json___lambda__1___closed__4 = _init_l_lean_process__file__json___lambda__1___closed__4();
 l_lean_process__file__json___lambda__1___closed__5 = _init_l_lean_process__file__json___lambda__1___closed__5();
 l_lean_process__file__json___lambda__1___closed__6 = _init_l_lean_process__file__json___lambda__1___closed__6();
 l_lean_process__file__json___lambda__1___closed__7 = _init_l_lean_process__file__json___lambda__1___closed__7();
 l_lean_process__file__json___lambda__1___closed__8 = _init_l_lean_process__file__json___lambda__1___closed__8();
 l_lean_process__file__json___lambda__1___closed__9 = _init_l_lean_process__file__json___lambda__1___closed__9();
}

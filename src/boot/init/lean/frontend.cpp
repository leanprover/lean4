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
obj* l_lean_parser_tokens(obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
extern obj* l_lean_message__log_empty;
obj* l_lean_run__expander(obj*, obj*);
obj* l_lean_mk__config(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser), 3, 0);
x_3 = l_lean_parser_module_tokens;
x_4 = l_lean_parser_tokens(lean::box(0), x_2);
lean::inc(x_3);
x_6 = lean::apply_1(x_4, x_3);
x_7 = l_lean_parser_command_builtin__command__parsers;
x_8 = l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
lean::inc(x_7);
x_10 = l_lean_parser_tokens(lean::box(0), x_7);
lean::inc(x_8);
x_12 = lean::apply_1(x_10, x_8);
x_13 = l_list_append___main___rarg(x_6, x_12);
x_14 = l_lean_parser_term_builtin__leading__parsers;
x_15 = l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
lean::inc(x_14);
x_17 = l_lean_parser_tokens(lean::box(0), x_14);
lean::inc(x_15);
x_19 = lean::apply_1(x_17, x_15);
x_20 = l_list_append___main___rarg(x_13, x_19);
x_21 = l_lean_parser_term_builtin__trailing__parsers;
x_22 = l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
lean::inc(x_21);
x_24 = l_lean_parser_tokens(lean::box(0), x_21);
lean::inc(x_22);
x_26 = lean::apply_1(x_24, x_22);
x_27 = l_list_append___main___rarg(x_20, x_26);
x_28 = l_lean_parser_mk__token__trie(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_14);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_21);
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_36 = x_28;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_49; obj* x_51; obj* x_52; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_40 = x_28;
}
lean::inc(x_1);
x_42 = l_lean_file__map_from__string(x_1);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_0);
lean::cnstr_set(x_43, 1, x_1);
lean::cnstr_set(x_43, 2, x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_38);
x_45 = lean::alloc_cnstr(0, 0, 0);
;
lean::inc(x_45);
lean::inc(x_21);
lean::inc(x_14);
x_49 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_14);
lean::cnstr_set(x_49, 2, x_21);
lean::cnstr_set(x_49, 3, x_45);
lean::cnstr_set(x_49, 4, x_45);
lean::inc(x_7);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_7);
if (lean::is_scalar(x_40)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_40;
}
lean::cnstr_set(x_52, 0, x_51);
return x_52;
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
unsigned char x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; 
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
x_27 = l_lean_run__parser(lean::box(0), lean::box(0));
lean::inc(x_16);
x_29 = lean::apply_2(x_27, x_26, x_16);
if (lean::obj_tag(x_29) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_29);
x_38 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__1;
lean::inc(x_38);
x_40 = l_io_println___at_lean_run__frontend___spec__3(x_38, x_2);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_23);
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_49 = x_41;
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
x_3 = x_50;
x_4 = x_43;
goto lbl_5;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_51 = x_41;
}
x_52 = l_list_reverse___rarg(x_23);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
if (lean::is_scalar(x_51)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_51;
}
lean::cnstr_set(x_54, 0, x_53);
x_3 = x_54;
x_4 = x_43;
goto lbl_5;
}
}
else
{
obj* x_55; obj* x_57; obj* x_60; obj* x_62; 
x_55 = lean::cnstr_get(x_29, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_29, 1);
lean::inc(x_57);
lean::dec(x_29);
x_60 = lean::cnstr_get(x_55, 1);
lean::inc(x_60);
x_62 = l_list_reverse___rarg(x_60);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_70; 
lean::dec(x_62);
x_64 = lean::cnstr_get(x_55, 0);
lean::inc(x_64);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_66, 0, x_64);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_67, 0, x_66);
x_68 = l_lean_run__expander(lean::box(0), lean::box(0));
lean::inc(x_21);
x_70 = lean::apply_2(x_68, x_67, x_21);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_78; 
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_73 = x_70;
}
lean::inc(x_0);
x_75 = lean::apply_2(x_0, x_71, x_2);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_91; obj* x_94; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_57);
lean::dec(x_55);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_23);
x_91 = lean::cnstr_get(x_76, 0);
lean::inc(x_91);
lean::dec(x_76);
if (lean::is_scalar(x_73)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_73;
}
lean::cnstr_set(x_94, 0, x_91);
x_3 = x_94;
x_4 = x_78;
goto lbl_5;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_76);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_55);
lean::cnstr_set(x_96, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_10;
}
lean::cnstr_set(x_97, 0, x_21);
lean::cnstr_set(x_97, 1, x_96);
if (lean::is_scalar(x_15)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_15;
}
lean::cnstr_set(x_98, 0, x_16);
lean::cnstr_set(x_98, 1, x_97);
if (lean::is_scalar(x_20)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_20;
}
lean::cnstr_set(x_99, 0, x_11);
lean::cnstr_set(x_99, 1, x_98);
if (lean::is_scalar(x_25)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_25;
}
lean::cnstr_set(x_100, 0, x_57);
lean::cnstr_set(x_100, 1, x_99);
x_101 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
if (lean::is_scalar(x_73)) {
 x_102 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_102 = x_73;
}
lean::cnstr_set(x_102, 0, x_101);
x_3 = x_102;
x_4 = x_78;
goto lbl_5;
}
}
else
{
obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_111; 
lean::dec(x_16);
lean::dec(x_21);
x_105 = lean::cnstr_get(x_70, 0);
lean::inc(x_105);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_107 = x_70;
}
x_108 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_108, 0, x_11);
x_109 = l_lean_run__elaborator(lean::box(0), lean::box(0));
lean::inc(x_105);
x_111 = lean::apply_2(x_109, x_108, x_105);
if (lean::obj_tag(x_111) == 0)
{
obj* x_117; obj* x_120; unsigned char x_122; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_57);
lean::dec(x_10);
lean::dec(x_20);
x_117 = lean::cnstr_get(x_111, 0);
lean::inc(x_117);
lean::dec(x_111);
x_120 = l_lean_parser_module_eoi;
lean::inc(x_120);
x_122 = l_lean_parser_syntax_is__of__kind___main(x_120, x_105);
if (x_122 == 0)
{
obj* x_123; obj* x_125; obj* x_126; obj* x_128; 
x_123 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_123);
x_125 = l_io_println___at_lean_run__frontend___spec__3(x_123, x_2);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_134; obj* x_137; 
lean::dec(x_117);
lean::dec(x_55);
lean::dec(x_23);
x_134 = lean::cnstr_get(x_126, 0);
lean::inc(x_134);
lean::dec(x_126);
if (lean::is_scalar(x_107)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_107;
}
lean::cnstr_set(x_137, 0, x_134);
x_3 = x_137;
x_4 = x_128;
goto lbl_5;
}
else
{
obj* x_139; obj* x_141; obj* x_142; obj* x_144; 
lean::dec(x_126);
x_139 = l_list_reverse___rarg(x_117);
lean::inc(x_0);
x_141 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__7(x_0, x_139, x_128);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
lean::dec(x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_149; obj* x_152; 
lean::dec(x_55);
lean::dec(x_23);
x_149 = lean::cnstr_get(x_142, 0);
lean::inc(x_149);
lean::dec(x_142);
if (lean::is_scalar(x_107)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_107;
}
lean::cnstr_set(x_152, 0, x_149);
x_3 = x_152;
x_4 = x_144;
goto lbl_5;
}
else
{
obj* x_154; obj* x_155; obj* x_157; obj* x_160; obj* x_161; obj* x_163; obj* x_165; obj* x_166; obj* x_167; obj* x_170; obj* x_173; obj* x_174; obj* x_176; obj* x_177; unsigned char x_178; obj* x_179; obj* x_183; obj* x_184; obj* x_186; obj* x_187; obj* x_189; 
lean::dec(x_142);
x_154 = lean::alloc_cnstr(0, 0, 0);
;
x_155 = lean::cnstr_get(x_55, 2);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_155, 1);
lean::inc(x_157);
lean::inc(x_157);
x_160 = l_nat_repr(x_157);
x_161 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_161);
x_163 = lean::string_append(x_161, x_160);
lean::dec(x_160);
x_165 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_166 = lean::string_append(x_163, x_165);
x_167 = lean::cnstr_get(x_155, 2);
lean::inc(x_167);
lean::dec(x_155);
x_170 = lean::nat_add(x_157, x_167);
lean::dec(x_167);
lean::dec(x_157);
x_173 = l_nat_repr(x_170);
x_174 = lean::string_append(x_166, x_173);
lean::dec(x_173);
x_176 = l_lean_run__frontend___closed__1;
x_177 = l_lean_elaborator_notation_elaborate___closed__1;
x_178 = 0;
x_179 = l_string_join___closed__1;
lean::inc(x_179);
lean::inc(x_177);
lean::inc(x_176);
x_183 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_183, 0, x_176);
lean::cnstr_set(x_183, 1, x_177);
lean::cnstr_set(x_183, 2, x_154);
lean::cnstr_set(x_183, 3, x_179);
lean::cnstr_set(x_183, 4, x_174);
lean::cnstr_set_scalar(x_183, sizeof(void*)*5, x_178);
x_184 = x_183;
lean::inc(x_0);
x_186 = lean::apply_2(x_0, x_184, x_144);
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
lean::dec(x_186);
if (lean::obj_tag(x_187) == 0)
{
obj* x_194; obj* x_197; 
lean::dec(x_55);
lean::dec(x_23);
x_194 = lean::cnstr_get(x_187, 0);
lean::inc(x_194);
lean::dec(x_187);
if (lean::is_scalar(x_107)) {
 x_197 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_197 = x_107;
}
lean::cnstr_set(x_197, 0, x_194);
x_3 = x_197;
x_4 = x_189;
goto lbl_5;
}
else
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
lean::dec(x_187);
x_199 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_199, 0, x_55);
lean::cnstr_set(x_199, 1, x_23);
x_200 = l_list_reverse___rarg(x_199);
x_201 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_201, 0, x_200);
if (lean::is_scalar(x_107)) {
 x_202 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_202 = x_107;
}
lean::cnstr_set(x_202, 0, x_201);
x_3 = x_202;
x_4 = x_189;
goto lbl_5;
}
}
}
}
else
{
obj* x_203; obj* x_205; obj* x_206; obj* x_208; 
x_203 = l_list_reverse___rarg(x_117);
lean::inc(x_0);
x_205 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__8(x_0, x_203, x_2);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_205, 1);
lean::inc(x_208);
lean::dec(x_205);
if (lean::obj_tag(x_206) == 0)
{
obj* x_213; obj* x_216; 
lean::dec(x_55);
lean::dec(x_23);
x_213 = lean::cnstr_get(x_206, 0);
lean::inc(x_213);
lean::dec(x_206);
if (lean::is_scalar(x_107)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_107;
}
lean::cnstr_set(x_216, 0, x_213);
x_3 = x_216;
x_4 = x_208;
goto lbl_5;
}
else
{
obj* x_218; obj* x_219; obj* x_221; obj* x_224; obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_231; obj* x_234; obj* x_237; obj* x_238; obj* x_240; obj* x_241; unsigned char x_242; obj* x_243; obj* x_247; obj* x_248; obj* x_250; obj* x_251; obj* x_253; 
lean::dec(x_206);
x_218 = lean::alloc_cnstr(0, 0, 0);
;
x_219 = lean::cnstr_get(x_55, 2);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_219, 1);
lean::inc(x_221);
lean::inc(x_221);
x_224 = l_nat_repr(x_221);
x_225 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_225);
x_227 = lean::string_append(x_225, x_224);
lean::dec(x_224);
x_229 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_230 = lean::string_append(x_227, x_229);
x_231 = lean::cnstr_get(x_219, 2);
lean::inc(x_231);
lean::dec(x_219);
x_234 = lean::nat_add(x_221, x_231);
lean::dec(x_231);
lean::dec(x_221);
x_237 = l_nat_repr(x_234);
x_238 = lean::string_append(x_230, x_237);
lean::dec(x_237);
x_240 = l_lean_run__frontend___closed__1;
x_241 = l_lean_elaborator_notation_elaborate___closed__1;
x_242 = 0;
x_243 = l_string_join___closed__1;
lean::inc(x_243);
lean::inc(x_241);
lean::inc(x_240);
x_247 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_247, 0, x_240);
lean::cnstr_set(x_247, 1, x_241);
lean::cnstr_set(x_247, 2, x_218);
lean::cnstr_set(x_247, 3, x_243);
lean::cnstr_set(x_247, 4, x_238);
lean::cnstr_set_scalar(x_247, sizeof(void*)*5, x_242);
x_248 = x_247;
lean::inc(x_0);
x_250 = lean::apply_2(x_0, x_248, x_208);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
if (lean::obj_tag(x_251) == 0)
{
obj* x_258; obj* x_261; 
lean::dec(x_55);
lean::dec(x_23);
x_258 = lean::cnstr_get(x_251, 0);
lean::inc(x_258);
lean::dec(x_251);
if (lean::is_scalar(x_107)) {
 x_261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_261 = x_107;
}
lean::cnstr_set(x_261, 0, x_258);
x_3 = x_261;
x_4 = x_253;
goto lbl_5;
}
else
{
obj* x_263; obj* x_264; obj* x_265; obj* x_266; 
lean::dec(x_251);
x_263 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_263, 0, x_55);
lean::cnstr_set(x_263, 1, x_23);
x_264 = l_list_reverse___rarg(x_263);
x_265 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_265, 0, x_264);
if (lean::is_scalar(x_107)) {
 x_266 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_266 = x_107;
}
lean::cnstr_set(x_266, 0, x_265);
x_3 = x_266;
x_4 = x_253;
goto lbl_5;
}
}
}
}
else
{
obj* x_268; obj* x_270; obj* x_273; obj* x_275; obj* x_277; obj* x_278; obj* x_280; 
lean::dec(x_105);
x_268 = lean::cnstr_get(x_111, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get(x_111, 1);
lean::inc(x_270);
lean::dec(x_111);
x_273 = lean::cnstr_get(x_268, 5);
lean::inc(x_273);
x_275 = l_list_reverse___rarg(x_273);
lean::inc(x_0);
x_277 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__9(x_0, x_275, x_2);
x_278 = lean::cnstr_get(x_277, 0);
lean::inc(x_278);
x_280 = lean::cnstr_get(x_277, 1);
lean::inc(x_280);
lean::dec(x_277);
if (lean::obj_tag(x_278) == 0)
{
obj* x_292; obj* x_295; 
lean::dec(x_270);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_57);
lean::dec(x_55);
lean::dec(x_268);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_23);
x_292 = lean::cnstr_get(x_278, 0);
lean::inc(x_292);
lean::dec(x_278);
if (lean::is_scalar(x_107)) {
 x_295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_295 = x_107;
}
lean::cnstr_set(x_295, 0, x_292);
x_3 = x_295;
x_4 = x_280;
goto lbl_5;
}
else
{
obj* x_297; obj* x_299; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; 
lean::dec(x_278);
x_297 = lean::cnstr_get(x_268, 6);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_268, 7);
lean::inc(x_299);
lean::dec(x_268);
x_302 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_302, 0, x_55);
lean::cnstr_set(x_302, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_10;
}
lean::cnstr_set(x_303, 0, x_299);
lean::cnstr_set(x_303, 1, x_302);
if (lean::is_scalar(x_15)) {
 x_304 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_304 = x_15;
}
lean::cnstr_set(x_304, 0, x_297);
lean::cnstr_set(x_304, 1, x_303);
if (lean::is_scalar(x_20)) {
 x_305 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_305 = x_20;
}
lean::cnstr_set(x_305, 0, x_270);
lean::cnstr_set(x_305, 1, x_304);
if (lean::is_scalar(x_25)) {
 x_306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_306 = x_25;
}
lean::cnstr_set(x_306, 0, x_57);
lean::cnstr_set(x_306, 1, x_305);
x_307 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_307, 0, x_306);
if (lean::is_scalar(x_107)) {
 x_308 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_308 = x_107;
}
lean::cnstr_set(x_308, 0, x_307);
x_3 = x_308;
x_4 = x_280;
goto lbl_5;
}
}
}
}
else
{
obj* x_310; obj* x_311; obj* x_313; 
lean::inc(x_0);
x_310 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__10(x_0, x_62, x_2);
x_311 = lean::cnstr_get(x_310, 0);
lean::inc(x_311);
x_313 = lean::cnstr_get(x_310, 1);
lean::inc(x_313);
lean::dec(x_310);
if (lean::obj_tag(x_311) == 0)
{
obj* x_326; obj* x_328; obj* x_329; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_57);
lean::dec(x_55);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_23);
x_326 = lean::cnstr_get(x_311, 0);
lean::inc(x_326);
if (lean::is_shared(x_311)) {
 lean::dec(x_311);
 x_328 = lean::box(0);
} else {
 lean::cnstr_release(x_311, 0);
 x_328 = x_311;
}
if (lean::is_scalar(x_328)) {
 x_329 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_329 = x_328;
}
lean::cnstr_set(x_329, 0, x_326);
x_3 = x_329;
x_4 = x_313;
goto lbl_5;
}
else
{
obj* x_330; obj* x_331; obj* x_333; obj* x_334; obj* x_335; obj* x_337; 
if (lean::is_shared(x_311)) {
 lean::dec(x_311);
 x_330 = lean::box(0);
} else {
 lean::cnstr_release(x_311, 0);
 x_330 = x_311;
}
x_331 = lean::cnstr_get(x_55, 0);
lean::inc(x_331);
x_333 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_expander_expand), 2, 1);
lean::closure_set(x_333, 0, x_331);
x_334 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_run___rarg), 2, 1);
lean::closure_set(x_334, 0, x_333);
x_335 = l_lean_run__expander(lean::box(0), lean::box(0));
lean::inc(x_21);
x_337 = lean::apply_2(x_335, x_334, x_21);
if (lean::obj_tag(x_337) == 0)
{
obj* x_338; obj* x_342; obj* x_343; obj* x_345; 
x_338 = lean::cnstr_get(x_337, 0);
lean::inc(x_338);
lean::dec(x_337);
lean::inc(x_0);
x_342 = lean::apply_2(x_0, x_338, x_313);
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_342, 1);
lean::inc(x_345);
lean::dec(x_342);
if (lean::obj_tag(x_343) == 0)
{
obj* x_358; obj* x_361; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_16);
lean::dec(x_57);
lean::dec(x_55);
lean::dec(x_10);
lean::dec(x_11);
lean::dec(x_20);
lean::dec(x_21);
lean::dec(x_23);
x_358 = lean::cnstr_get(x_343, 0);
lean::inc(x_358);
lean::dec(x_343);
if (lean::is_scalar(x_330)) {
 x_361 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_361 = x_330;
}
lean::cnstr_set(x_361, 0, x_358);
x_3 = x_361;
x_4 = x_345;
goto lbl_5;
}
else
{
obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; 
lean::dec(x_343);
x_363 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_363, 0, x_55);
lean::cnstr_set(x_363, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_364 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_364 = x_10;
}
lean::cnstr_set(x_364, 0, x_21);
lean::cnstr_set(x_364, 1, x_363);
if (lean::is_scalar(x_15)) {
 x_365 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_365 = x_15;
}
lean::cnstr_set(x_365, 0, x_16);
lean::cnstr_set(x_365, 1, x_364);
if (lean::is_scalar(x_20)) {
 x_366 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_366 = x_20;
}
lean::cnstr_set(x_366, 0, x_11);
lean::cnstr_set(x_366, 1, x_365);
if (lean::is_scalar(x_25)) {
 x_367 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_367 = x_25;
}
lean::cnstr_set(x_367, 0, x_57);
lean::cnstr_set(x_367, 1, x_366);
x_368 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_368, 0, x_367);
if (lean::is_scalar(x_330)) {
 x_369 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_369 = x_330;
}
lean::cnstr_set(x_369, 0, x_368);
x_3 = x_369;
x_4 = x_345;
goto lbl_5;
}
}
else
{
obj* x_372; obj* x_375; obj* x_376; obj* x_378; 
lean::dec(x_16);
lean::dec(x_21);
x_372 = lean::cnstr_get(x_337, 0);
lean::inc(x_372);
lean::dec(x_337);
x_375 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_resume___rarg), 2, 1);
lean::closure_set(x_375, 0, x_11);
x_376 = l_lean_run__elaborator(lean::box(0), lean::box(0));
lean::inc(x_372);
x_378 = lean::apply_2(x_376, x_375, x_372);
if (lean::obj_tag(x_378) == 0)
{
obj* x_384; obj* x_387; unsigned char x_389; 
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_57);
lean::dec(x_10);
lean::dec(x_20);
x_384 = lean::cnstr_get(x_378, 0);
lean::inc(x_384);
lean::dec(x_378);
x_387 = l_lean_parser_module_eoi;
lean::inc(x_387);
x_389 = l_lean_parser_syntax_is__of__kind___main(x_387, x_372);
if (x_389 == 0)
{
obj* x_390; obj* x_392; obj* x_393; obj* x_395; 
x_390 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__2;
lean::inc(x_390);
x_392 = l_io_println___at_lean_run__frontend___spec__3(x_390, x_313);
x_393 = lean::cnstr_get(x_392, 0);
lean::inc(x_393);
x_395 = lean::cnstr_get(x_392, 1);
lean::inc(x_395);
lean::dec(x_392);
if (lean::obj_tag(x_393) == 0)
{
obj* x_401; obj* x_404; 
lean::dec(x_55);
lean::dec(x_384);
lean::dec(x_23);
x_401 = lean::cnstr_get(x_393, 0);
lean::inc(x_401);
lean::dec(x_393);
if (lean::is_scalar(x_330)) {
 x_404 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_404 = x_330;
}
lean::cnstr_set(x_404, 0, x_401);
x_3 = x_404;
x_4 = x_395;
goto lbl_5;
}
else
{
obj* x_406; obj* x_408; obj* x_409; obj* x_411; 
lean::dec(x_393);
x_406 = l_list_reverse___rarg(x_384);
lean::inc(x_0);
x_408 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__11(x_0, x_406, x_395);
x_409 = lean::cnstr_get(x_408, 0);
lean::inc(x_409);
x_411 = lean::cnstr_get(x_408, 1);
lean::inc(x_411);
lean::dec(x_408);
if (lean::obj_tag(x_409) == 0)
{
obj* x_416; obj* x_419; 
lean::dec(x_55);
lean::dec(x_23);
x_416 = lean::cnstr_get(x_409, 0);
lean::inc(x_416);
lean::dec(x_409);
if (lean::is_scalar(x_330)) {
 x_419 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_419 = x_330;
}
lean::cnstr_set(x_419, 0, x_416);
x_3 = x_419;
x_4 = x_411;
goto lbl_5;
}
else
{
obj* x_421; obj* x_422; obj* x_424; obj* x_427; obj* x_428; obj* x_430; obj* x_432; obj* x_433; obj* x_434; obj* x_437; obj* x_440; obj* x_441; obj* x_443; obj* x_444; unsigned char x_445; obj* x_446; obj* x_450; obj* x_451; obj* x_453; obj* x_454; obj* x_456; 
lean::dec(x_409);
x_421 = lean::alloc_cnstr(0, 0, 0);
;
x_422 = lean::cnstr_get(x_55, 2);
lean::inc(x_422);
x_424 = lean::cnstr_get(x_422, 1);
lean::inc(x_424);
lean::inc(x_424);
x_427 = l_nat_repr(x_424);
x_428 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_428);
x_430 = lean::string_append(x_428, x_427);
lean::dec(x_427);
x_432 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_433 = lean::string_append(x_430, x_432);
x_434 = lean::cnstr_get(x_422, 2);
lean::inc(x_434);
lean::dec(x_422);
x_437 = lean::nat_add(x_424, x_434);
lean::dec(x_434);
lean::dec(x_424);
x_440 = l_nat_repr(x_437);
x_441 = lean::string_append(x_433, x_440);
lean::dec(x_440);
x_443 = l_lean_run__frontend___closed__1;
x_444 = l_lean_elaborator_notation_elaborate___closed__1;
x_445 = 0;
x_446 = l_string_join___closed__1;
lean::inc(x_446);
lean::inc(x_444);
lean::inc(x_443);
x_450 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_450, 0, x_443);
lean::cnstr_set(x_450, 1, x_444);
lean::cnstr_set(x_450, 2, x_421);
lean::cnstr_set(x_450, 3, x_446);
lean::cnstr_set(x_450, 4, x_441);
lean::cnstr_set_scalar(x_450, sizeof(void*)*5, x_445);
x_451 = x_450;
lean::inc(x_0);
x_453 = lean::apply_2(x_0, x_451, x_411);
x_454 = lean::cnstr_get(x_453, 0);
lean::inc(x_454);
x_456 = lean::cnstr_get(x_453, 1);
lean::inc(x_456);
lean::dec(x_453);
if (lean::obj_tag(x_454) == 0)
{
obj* x_461; obj* x_464; 
lean::dec(x_55);
lean::dec(x_23);
x_461 = lean::cnstr_get(x_454, 0);
lean::inc(x_461);
lean::dec(x_454);
if (lean::is_scalar(x_330)) {
 x_464 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_464 = x_330;
}
lean::cnstr_set(x_464, 0, x_461);
x_3 = x_464;
x_4 = x_456;
goto lbl_5;
}
else
{
obj* x_466; obj* x_467; obj* x_468; obj* x_469; 
lean::dec(x_454);
x_466 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_466, 0, x_55);
lean::cnstr_set(x_466, 1, x_23);
x_467 = l_list_reverse___rarg(x_466);
x_468 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_468, 0, x_467);
if (lean::is_scalar(x_330)) {
 x_469 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_469 = x_330;
}
lean::cnstr_set(x_469, 0, x_468);
x_3 = x_469;
x_4 = x_456;
goto lbl_5;
}
}
}
}
else
{
obj* x_470; obj* x_472; obj* x_473; obj* x_475; 
x_470 = l_list_reverse___rarg(x_384);
lean::inc(x_0);
x_472 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__12(x_0, x_470, x_313);
x_473 = lean::cnstr_get(x_472, 0);
lean::inc(x_473);
x_475 = lean::cnstr_get(x_472, 1);
lean::inc(x_475);
lean::dec(x_472);
if (lean::obj_tag(x_473) == 0)
{
obj* x_480; obj* x_483; 
lean::dec(x_55);
lean::dec(x_23);
x_480 = lean::cnstr_get(x_473, 0);
lean::inc(x_480);
lean::dec(x_473);
if (lean::is_scalar(x_330)) {
 x_483 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_483 = x_330;
}
lean::cnstr_set(x_483, 0, x_480);
x_3 = x_483;
x_4 = x_475;
goto lbl_5;
}
else
{
obj* x_485; obj* x_486; obj* x_488; obj* x_491; obj* x_492; obj* x_494; obj* x_496; obj* x_497; obj* x_498; obj* x_501; obj* x_504; obj* x_505; obj* x_507; obj* x_508; unsigned char x_509; obj* x_510; obj* x_514; obj* x_515; obj* x_517; obj* x_518; obj* x_520; 
lean::dec(x_473);
x_485 = lean::alloc_cnstr(0, 0, 0);
;
x_486 = lean::cnstr_get(x_55, 2);
lean::inc(x_486);
x_488 = lean::cnstr_get(x_486, 1);
lean::inc(x_488);
lean::inc(x_488);
x_491 = l_nat_repr(x_488);
x_492 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__3;
lean::inc(x_492);
x_494 = lean::string_append(x_492, x_491);
lean::dec(x_491);
x_496 = l_io_prim_iterate___main___at_lean_run__frontend___spec__15___closed__4;
x_497 = lean::string_append(x_494, x_496);
x_498 = lean::cnstr_get(x_486, 2);
lean::inc(x_498);
lean::dec(x_486);
x_501 = lean::nat_add(x_488, x_498);
lean::dec(x_498);
lean::dec(x_488);
x_504 = l_nat_repr(x_501);
x_505 = lean::string_append(x_497, x_504);
lean::dec(x_504);
x_507 = l_lean_run__frontend___closed__1;
x_508 = l_lean_elaborator_notation_elaborate___closed__1;
x_509 = 0;
x_510 = l_string_join___closed__1;
lean::inc(x_510);
lean::inc(x_508);
lean::inc(x_507);
x_514 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_514, 0, x_507);
lean::cnstr_set(x_514, 1, x_508);
lean::cnstr_set(x_514, 2, x_485);
lean::cnstr_set(x_514, 3, x_510);
lean::cnstr_set(x_514, 4, x_505);
lean::cnstr_set_scalar(x_514, sizeof(void*)*5, x_509);
x_515 = x_514;
lean::inc(x_0);
x_517 = lean::apply_2(x_0, x_515, x_475);
x_518 = lean::cnstr_get(x_517, 0);
lean::inc(x_518);
x_520 = lean::cnstr_get(x_517, 1);
lean::inc(x_520);
lean::dec(x_517);
if (lean::obj_tag(x_518) == 0)
{
obj* x_525; obj* x_528; 
lean::dec(x_55);
lean::dec(x_23);
x_525 = lean::cnstr_get(x_518, 0);
lean::inc(x_525);
lean::dec(x_518);
if (lean::is_scalar(x_330)) {
 x_528 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_528 = x_330;
}
lean::cnstr_set(x_528, 0, x_525);
x_3 = x_528;
x_4 = x_520;
goto lbl_5;
}
else
{
obj* x_530; obj* x_531; obj* x_532; obj* x_533; 
lean::dec(x_518);
x_530 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_530, 0, x_55);
lean::cnstr_set(x_530, 1, x_23);
x_531 = l_list_reverse___rarg(x_530);
x_532 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_532, 0, x_531);
if (lean::is_scalar(x_330)) {
 x_533 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_533 = x_330;
}
lean::cnstr_set(x_533, 0, x_532);
x_3 = x_533;
x_4 = x_520;
goto lbl_5;
}
}
}
}
else
{
obj* x_535; obj* x_537; obj* x_540; obj* x_542; obj* x_544; obj* x_545; obj* x_547; 
lean::dec(x_372);
x_535 = lean::cnstr_get(x_378, 0);
lean::inc(x_535);
x_537 = lean::cnstr_get(x_378, 1);
lean::inc(x_537);
lean::dec(x_378);
x_540 = lean::cnstr_get(x_535, 5);
lean::inc(x_540);
x_542 = l_list_reverse___rarg(x_540);
lean::inc(x_0);
x_544 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__13(x_0, x_542, x_313);
x_545 = lean::cnstr_get(x_544, 0);
lean::inc(x_545);
x_547 = lean::cnstr_get(x_544, 1);
lean::inc(x_547);
lean::dec(x_544);
if (lean::obj_tag(x_545) == 0)
{
obj* x_559; obj* x_562; 
lean::dec(x_535);
lean::dec(x_537);
lean::dec(x_25);
lean::dec(x_15);
lean::dec(x_57);
lean::dec(x_55);
lean::dec(x_10);
lean::dec(x_20);
lean::dec(x_23);
x_559 = lean::cnstr_get(x_545, 0);
lean::inc(x_559);
lean::dec(x_545);
if (lean::is_scalar(x_330)) {
 x_562 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_562 = x_330;
}
lean::cnstr_set(x_562, 0, x_559);
x_3 = x_562;
x_4 = x_547;
goto lbl_5;
}
else
{
obj* x_564; obj* x_566; obj* x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; 
lean::dec(x_545);
x_564 = lean::cnstr_get(x_535, 6);
lean::inc(x_564);
x_566 = lean::cnstr_get(x_535, 7);
lean::inc(x_566);
lean::dec(x_535);
x_569 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_569, 0, x_55);
lean::cnstr_set(x_569, 1, x_23);
if (lean::is_scalar(x_10)) {
 x_570 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_570 = x_10;
}
lean::cnstr_set(x_570, 0, x_566);
lean::cnstr_set(x_570, 1, x_569);
if (lean::is_scalar(x_15)) {
 x_571 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_571 = x_15;
}
lean::cnstr_set(x_571, 0, x_564);
lean::cnstr_set(x_571, 1, x_570);
if (lean::is_scalar(x_20)) {
 x_572 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_572 = x_20;
}
lean::cnstr_set(x_572, 0, x_537);
lean::cnstr_set(x_572, 1, x_571);
if (lean::is_scalar(x_25)) {
 x_573 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_573 = x_25;
}
lean::cnstr_set(x_573, 0, x_57);
lean::cnstr_set(x_573, 1, x_572);
x_574 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_574, 0, x_573);
if (lean::is_scalar(x_330)) {
 x_575 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_575 = x_330;
}
lean::cnstr_set(x_575, 0, x_574);
x_3 = x_575;
x_4 = x_547;
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
obj* x_577; obj* x_579; obj* x_580; obj* x_581; 
lean::dec(x_0);
x_577 = lean::cnstr_get(x_3, 0);
lean::inc(x_577);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_579 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_579 = x_3;
}
if (lean::is_scalar(x_579)) {
 x_580 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_580 = x_579;
}
lean::cnstr_set(x_580, 0, x_577);
x_581 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_581, 0, x_580);
lean::cnstr_set(x_581, 1, x_4);
return x_581;
}
else
{
obj* x_582; obj* x_584; 
x_582 = lean::cnstr_get(x_3, 0);
lean::inc(x_582);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_584 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_584 = x_3;
}
if (lean::obj_tag(x_582) == 0)
{
obj* x_586; 
lean::dec(x_584);
x_586 = lean::cnstr_get(x_582, 0);
lean::inc(x_586);
lean::dec(x_582);
x_1 = x_586;
x_2 = x_4;
goto _start;
}
else
{
obj* x_591; obj* x_594; obj* x_595; 
lean::dec(x_0);
x_591 = lean::cnstr_get(x_582, 0);
lean::inc(x_591);
lean::dec(x_582);
if (lean::is_scalar(x_584)) {
 x_594 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_594 = x_584;
}
lean::cnstr_set(x_594, 0, x_591);
x_595 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_595, 0, x_594);
lean::cnstr_set(x_595, 1, x_4);
return x_595;
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
x_21 = lean::alloc_cnstr(0, 0, 0);
;
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

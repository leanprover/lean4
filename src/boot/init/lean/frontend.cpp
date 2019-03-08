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
obj* l_lean_run__frontend__aux___main___lambda__2___boxed(obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3___boxed(obj*, obj*);
obj* l_lean_run__frontend__aux___main___lambda__2(obj*, obj*, obj*);
obj* l_lean_run__frontend__aux___main___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_run__frontend___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_expander_expand(obj*, obj*);
extern obj* l_lean_elaborator_notation_elaborate___closed__1;
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_run__frontend__aux___main___closed__2;
obj* l_lean_process__file___lambda__1___closed__6;
obj* l_lean_run__frontend__aux___main___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3(obj*, obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__3;
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_lean_parser_parse__command(obj*, obj*);
extern obj* l_lean_expander_expand__bracketed__binder___main___closed__4;
obj* l_string_quote(obj*);
extern obj* l_lean_expander_builtin__transformers;
obj* l_lean_mk__config(obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__5;
obj* l_lean_process__file___lambda__1___closed__8;
obj* lean_process_file(obj*, obj*, uint8, obj*);
obj* l_lean_run__frontend(obj*, obj*, obj*, uint8, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_process__file___lambda__1___closed__2;
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj*, obj*, obj*);
obj* l_lean_kvmap_set__bool(obj*, obj*, uint8);
obj* l_lean_process__file___closed__1;
obj* l_lean_run__frontend___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers_lean_parser_has__tokens;
extern obj* l_lean_parser_term_builtin__leading__parsers;
obj* l_lean_process__file___lambda__1___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
extern obj* l_lean_parser_module_eoi;
obj* l_io_println___at_lean_process__file___spec__1___boxed(obj*, obj*);
obj* l_lean_run__frontend__aux(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_lean_run__frontend__aux___main___lambda__3(obj*, obj*, obj*, obj*);
obj* l_io_print___at_lean_process__file___spec__2___boxed(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_io_println___at_lean_process__file___spec__1(obj*, obj*);
extern obj* l_lean_options_mk;
obj* l_lean_run__frontend__aux___main___closed__4;
obj* l_lean_process__file___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_message_to__string(obj*);
obj* l_lean_process__file___lambda__1___closed__7;
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_lean_file__map_from__string(obj*);
extern obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_lean_run__frontend__aux___main___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_run__frontend__aux___main___closed__1;
obj* l_lean_process__file___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_term_builtin__leading__parsers_lean_parser_has__tokens;
obj* l_lean_parser_parse__header(obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__2(obj*, obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers;
obj* l_lean_elaborator_mk__state(obj*, obj*);
extern obj* l_lean_parser_command_builtin__command__parsers_lean_parser_has__tokens;
obj* l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1;
extern obj* l_lean_parser_term_builtin__trailing__parsers;
obj* l_nat_repr(obj*);
obj* l_lean_elaborator_process__command(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1(obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__9;
obj* l_lean_run__frontend__aux___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_run__frontend__aux___main(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_print___at_lean_process__file___spec__2(obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_lean_run__frontend__aux___main___lambda__1(obj*, obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_run__frontend__aux___main___closed__3;
obj* l_lean_process__file___lambda__1(uint8, obj*, obj*);
obj* l_lean_profileit__pure___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_process__file___lambda__1___closed__4;
obj* l_lean_mk__config(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = l_lean_parser_module_header_parser_lean_parser_has__tokens;
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
obj* _init_l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1;
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
obj* l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1;
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
obj* l_lean_run__frontend__aux___main___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__command(x_0, x_1);
return x_3;
}
}
obj* l_lean_run__frontend__aux___main___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_expander_expand(x_0, x_1);
return x_3;
}
}
obj* l_lean_run__frontend__aux___main___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_elaborator_process__command(x_0, x_1, x_2);
return x_4;
}
}
obj* _init_l_lean_run__frontend__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("parsing");
return x_0;
}
}
obj* _init_l_lean_run__frontend__aux___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_list_reverse___rarg(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_run__frontend__aux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("expanding");
return x_0;
}
}
obj* _init_l_lean_run__frontend__aux___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("elaborating");
return x_0;
}
}
obj* l_lean_run__frontend__aux___main(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_14, 2);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
x_22 = lean::string_iterator_offset(x_20);
lean::dec(x_20);
x_24 = l_lean_file__map_to__position(x_17, x_22);
lean::inc(x_5);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__frontend__aux___main___lambda__1___boxed), 3, 2);
lean::closure_set(x_26, 0, x_5);
lean::closure_set(x_26, 1, x_3);
x_27 = l_lean_run__frontend__aux___main___closed__1;
x_28 = l_lean_profileit__pure___rarg(x_27, x_24, x_26, x_8);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_38; obj* x_41; obj* x_44; obj* x_47; obj* x_48; 
lean::dec(x_5);
lean::dec(x_24);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_2);
x_38 = lean::cnstr_get(x_28, 1);
lean::inc(x_38);
lean::dec(x_28);
x_41 = lean::cnstr_get(x_29, 0);
lean::inc(x_41);
lean::dec(x_29);
x_44 = lean::cnstr_get(x_31, 0);
lean::inc(x_44);
lean::dec(x_31);
x_47 = lean::apply_2(x_0, x_44, x_38);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_7);
lean::dec(x_41);
x_52 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_54 = x_47;
} else {
 lean::inc(x_52);
 lean::dec(x_47);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 x_57 = x_48;
} else {
 lean::inc(x_55);
 lean::dec(x_48);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
if (lean::is_scalar(x_54)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_54;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_52);
return x_59;
}
else
{
obj* x_60; 
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_60 = x_48;
} else {
 lean::dec(x_48);
 x_60 = lean::box(0);
}
if (x_1 == 0)
{
obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_7);
lean::dec(x_41);
lean::dec(x_60);
x_64 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_66 = x_47;
} else {
 lean::inc(x_64);
 lean::dec(x_47);
 x_66 = lean::box(0);
}
x_67 = l_lean_run__frontend__aux___main___closed__2;
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_71 = x_47;
} else {
 lean::inc(x_69);
 lean::dec(x_47);
 x_71 = lean::box(0);
}
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_41);
lean::cnstr_set(x_72, 1, x_7);
x_73 = l_list_reverse___rarg(x_72);
if (lean::is_scalar(x_60)) {
 x_74 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_74 = x_60;
}
lean::cnstr_set(x_74, 0, x_73);
if (lean::is_scalar(x_71)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_71;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_69);
return x_75;
}
}
}
else
{
obj* x_76; obj* x_79; obj* x_82; obj* x_85; obj* x_87; obj* x_90; obj* x_92; obj* x_93; 
x_76 = lean::cnstr_get(x_31, 0);
lean::inc(x_76);
lean::dec(x_31);
x_79 = lean::cnstr_get(x_28, 1);
lean::inc(x_79);
lean::dec(x_28);
x_82 = lean::cnstr_get(x_29, 0);
lean::inc(x_82);
lean::dec(x_29);
x_85 = lean::cnstr_get(x_76, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_76, 1);
lean::inc(x_87);
lean::dec(x_76);
x_90 = l_list_reverse___rarg(x_87);
lean::inc(x_0);
x_92 = l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1(x_0, x_90, x_79);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_5);
lean::dec(x_24);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_85);
lean::dec(x_82);
x_104 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_106 = x_92;
} else {
 lean::inc(x_104);
 lean::dec(x_92);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_109 = x_93;
} else {
 lean::inc(x_107);
 lean::dec(x_93);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
if (lean::is_scalar(x_106)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_106;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_104);
return x_111;
}
else
{
obj* x_113; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_93);
x_113 = lean::cnstr_get(x_92, 1);
lean::inc(x_113);
lean::dec(x_92);
lean::inc(x_6);
lean::inc(x_82);
x_118 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__frontend__aux___main___lambda__2___boxed), 3, 2);
lean::closure_set(x_118, 0, x_82);
lean::closure_set(x_118, 1, x_6);
x_119 = l_lean_run__frontend__aux___main___closed__3;
x_120 = l_lean_profileit__pure___rarg(x_119, x_24, x_118, x_113);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
if (lean::obj_tag(x_121) == 0)
{
lean::dec(x_24);
if (x_1 == 0)
{
obj* x_126; obj* x_129; obj* x_133; obj* x_134; 
lean::dec(x_7);
lean::dec(x_82);
x_126 = lean::cnstr_get(x_120, 1);
lean::inc(x_126);
lean::dec(x_120);
x_129 = lean::cnstr_get(x_121, 0);
lean::inc(x_129);
lean::dec(x_121);
lean::inc(x_0);
x_133 = lean::apply_2(x_0, x_129, x_126);
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
if (lean::obj_tag(x_134) == 0)
{
obj* x_142; obj* x_144; obj* x_145; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_85);
x_142 = lean::cnstr_get(x_133, 1);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 x_144 = x_133;
} else {
 lean::inc(x_142);
 lean::dec(x_133);
 x_144 = lean::box(0);
}
x_145 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_147 = x_134;
} else {
 lean::inc(x_145);
 lean::dec(x_134);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_145);
if (lean::is_scalar(x_144)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_144;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_142);
return x_149;
}
else
{
obj* x_151; obj* x_154; 
lean::dec(x_134);
x_151 = lean::cnstr_get(x_133, 1);
lean::inc(x_151);
lean::dec(x_133);
x_154 = lean::box(0);
x_3 = x_85;
x_7 = x_154;
x_8 = x_151;
goto _start;
}
}
else
{
obj* x_156; obj* x_159; obj* x_163; obj* x_164; 
x_156 = lean::cnstr_get(x_120, 1);
lean::inc(x_156);
lean::dec(x_120);
x_159 = lean::cnstr_get(x_121, 0);
lean::inc(x_159);
lean::dec(x_121);
lean::inc(x_0);
x_163 = lean::apply_2(x_0, x_159, x_156);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
if (lean::obj_tag(x_164) == 0)
{
obj* x_174; obj* x_176; obj* x_177; obj* x_179; obj* x_180; obj* x_181; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_85);
lean::dec(x_82);
x_174 = lean::cnstr_get(x_163, 1);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 x_176 = x_163;
} else {
 lean::inc(x_174);
 lean::dec(x_163);
 x_176 = lean::box(0);
}
x_177 = lean::cnstr_get(x_164, 0);
if (lean::is_exclusive(x_164)) {
 x_179 = x_164;
} else {
 lean::inc(x_177);
 lean::dec(x_164);
 x_179 = lean::box(0);
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
if (lean::is_scalar(x_176)) {
 x_181 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_181 = x_176;
}
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_174);
return x_181;
}
else
{
obj* x_183; obj* x_186; 
lean::dec(x_164);
x_183 = lean::cnstr_get(x_163, 1);
lean::inc(x_183);
lean::dec(x_163);
x_186 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_186, 0, x_82);
lean::cnstr_set(x_186, 1, x_7);
x_3 = x_85;
x_7 = x_186;
x_8 = x_183;
goto _start;
}
}
}
else
{
obj* x_190; obj* x_193; obj* x_195; obj* x_198; obj* x_199; obj* x_200; obj* x_202; obj* x_204; obj* x_206; obj* x_207; obj* x_209; obj* x_211; obj* x_212; obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_5);
lean::dec(x_6);
x_190 = lean::cnstr_get(x_120, 1);
lean::inc(x_190);
lean::dec(x_120);
x_193 = lean::cnstr_get(x_121, 0);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_set(x_121, 0, lean::box(0));
 x_195 = x_121;
} else {
 lean::inc(x_193);
 lean::dec(x_121);
 x_195 = lean::box(0);
}
lean::inc(x_193);
lean::inc(x_2);
x_198 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_run__frontend__aux___main___lambda__3___boxed), 4, 3);
lean::closure_set(x_198, 0, x_2);
lean::closure_set(x_198, 1, x_4);
lean::closure_set(x_198, 2, x_193);
x_199 = l_lean_run__frontend__aux___main___closed__4;
x_200 = l_lean_profileit__pure___rarg(x_199, x_24, x_198, x_190);
lean::dec(x_24);
x_202 = lean::cnstr_get(x_200, 0);
x_204 = lean::cnstr_get(x_200, 1);
if (lean::is_exclusive(x_200)) {
 lean::cnstr_set(x_200, 0, lean::box(0));
 lean::cnstr_set(x_200, 1, lean::box(0));
 x_206 = x_200;
} else {
 lean::inc(x_202);
 lean::inc(x_204);
 lean::dec(x_200);
 x_206 = lean::box(0);
}
x_207 = lean::cnstr_get(x_202, 5);
lean::inc(x_207);
x_209 = l_list_reverse___rarg(x_207);
lean::inc(x_0);
x_211 = l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__2(x_0, x_209, x_204);
x_212 = lean::cnstr_get(x_211, 0);
x_214 = lean::cnstr_get(x_211, 1);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_set(x_211, 0, lean::box(0));
 lean::cnstr_set(x_211, 1, lean::box(0));
 x_216 = x_211;
} else {
 lean::inc(x_212);
 lean::inc(x_214);
 lean::dec(x_211);
 x_216 = lean::box(0);
}
if (lean::obj_tag(x_212) == 0)
{
obj* x_228; obj* x_230; obj* x_231; obj* x_232; 
lean::dec(x_195);
lean::dec(x_193);
lean::dec(x_202);
lean::dec(x_216);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_85);
lean::dec(x_82);
x_228 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_230 = x_212;
} else {
 lean::inc(x_228);
 lean::dec(x_212);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_228);
if (lean::is_scalar(x_206)) {
 x_232 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_232 = x_206;
}
lean::cnstr_set(x_232, 0, x_231);
lean::cnstr_set(x_232, 1, x_214);
return x_232;
}
else
{
obj* x_235; uint8 x_236; 
lean::dec(x_212);
lean::dec(x_206);
x_235 = l_lean_parser_module_eoi;
x_236 = l_lean_parser_syntax_is__of__kind___main(x_235, x_193);
lean::dec(x_193);
if (x_236 == 0)
{
lean::dec(x_195);
lean::dec(x_216);
if (x_1 == 0)
{
obj* x_242; obj* x_244; obj* x_246; 
lean::dec(x_7);
lean::dec(x_82);
x_242 = lean::cnstr_get(x_202, 6);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_202, 7);
lean::inc(x_244);
x_246 = lean::box(0);
x_3 = x_85;
x_4 = x_202;
x_5 = x_242;
x_6 = x_244;
x_7 = x_246;
x_8 = x_214;
goto _start;
}
else
{
obj* x_248; obj* x_250; obj* x_252; 
x_248 = lean::cnstr_get(x_202, 6);
lean::inc(x_248);
x_250 = lean::cnstr_get(x_202, 7);
lean::inc(x_250);
x_252 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_252, 0, x_82);
lean::cnstr_set(x_252, 1, x_7);
x_3 = x_85;
x_4 = x_202;
x_5 = x_248;
x_6 = x_250;
x_7 = x_252;
x_8 = x_214;
goto _start;
}
}
else
{
obj* x_258; 
lean::dec(x_202);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_85);
x_258 = lean::box(0);
x_217 = x_258;
goto lbl_218;
}
}
lbl_218:
{
lean::dec(x_217);
if (x_1 == 0)
{
obj* x_263; obj* x_264; 
lean::dec(x_195);
lean::dec(x_7);
lean::dec(x_82);
x_263 = l_lean_run__frontend__aux___main___closed__2;
if (lean::is_scalar(x_216)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_216;
}
lean::cnstr_set(x_264, 0, x_263);
lean::cnstr_set(x_264, 1, x_214);
return x_264;
}
else
{
obj* x_265; obj* x_266; obj* x_267; obj* x_268; 
x_265 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_265, 0, x_82);
lean::cnstr_set(x_265, 1, x_7);
x_266 = l_list_reverse___rarg(x_265);
if (lean::is_scalar(x_195)) {
 x_267 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_267 = x_195;
}
lean::cnstr_set(x_267, 0, x_266);
if (lean::is_scalar(x_216)) {
 x_268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_268 = x_216;
}
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_214);
return x_268;
}
}
}
}
}
}
}
obj* l_lean_run__frontend__aux___main___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_run__frontend__aux___main___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_run__frontend__aux___main___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_run__frontend__aux___main___lambda__2(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_run__frontend__aux___main___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_run__frontend__aux___main___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_run__frontend__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_1);
x_10 = l_lean_run__frontend__aux___main(x_0, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
obj* l_lean_run__frontend__aux(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_lean_run__frontend__aux___main(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
obj* l_lean_run__frontend__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_1);
x_10 = l_lean_run__frontend__aux(x_0, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
obj* l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1;
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
obj* _init_l_lean_run__frontend___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("trace");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("as_messages");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = l_lean_options_mk;
x_6 = 1;
x_7 = l_lean_kvmap_set__bool(x_5, x_4, x_6);
return x_7;
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
obj* x_29; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_5, 0);
lean::inc(x_29);
lean::dec(x_5);
lean::inc(x_29);
x_33 = l_lean_parser_parse__header(x_29);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_34, 0);
lean::inc(x_40);
lean::dec(x_34);
x_43 = lean::apply_2(x_2, x_40, x_6);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_46 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_51 = x_44;
} else {
 lean::inc(x_49);
 lean::dec(x_44);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_48)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_48;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_44);
x_55 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_57 = x_43;
} else {
 lean::inc(x_55);
 lean::dec(x_43);
 x_57 = lean::box(0);
}
x_58 = l_lean_expander_expand__bracketed__binder___main___closed__4;
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
}
else
{
obj* x_60; obj* x_63; obj* x_65; obj* x_68; obj* x_70; obj* x_71; 
x_60 = lean::cnstr_get(x_34, 0);
lean::inc(x_60);
lean::dec(x_34);
x_63 = lean::cnstr_get(x_60, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 1);
lean::inc(x_65);
lean::dec(x_60);
x_68 = l_list_reverse___rarg(x_65);
lean::inc(x_2);
x_70 = l_list_mmap_x_27___main___at_lean_run__frontend___spec__1(x_2, x_68, x_6);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_63);
lean::dec(x_29);
x_78 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_80 = x_70;
} else {
 lean::inc(x_78);
 lean::dec(x_70);
 x_80 = lean::box(0);
}
x_81 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_83 = x_71;
} else {
 lean::inc(x_81);
 lean::dec(x_71);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_80)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_80;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_78);
return x_85;
}
else
{
obj* x_87; obj* x_90; obj* x_92; obj* x_95; obj* x_98; obj* x_100; obj* x_101; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_71);
x_87 = lean::cnstr_get(x_70, 1);
lean::inc(x_87);
lean::dec(x_70);
x_90 = lean::cnstr_get(x_29, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_90, 0);
lean::inc(x_92);
lean::dec(x_90);
x_95 = lean::cnstr_get(x_92, 0);
lean::inc(x_95);
lean::dec(x_92);
x_98 = l_lean_expander_builtin__transformers;
lean::inc(x_95);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_95);
lean::cnstr_set(x_100, 1, x_98);
x_101 = lean::cnstr_get(x_95, 2);
lean::inc(x_101);
lean::dec(x_95);
x_104 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_104, 0, x_0);
lean::cnstr_set(x_104, 1, x_1);
lean::cnstr_set(x_104, 2, x_101);
lean::inc(x_29);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_29);
x_107 = l_lean_run__frontend___closed__1;
lean::inc(x_106);
x_109 = l_lean_elaborator_mk__state(x_106, x_107);
x_110 = lean::box(0);
x_111 = l_lean_run__frontend__aux___main(x_2, x_3, x_106, x_63, x_109, x_29, x_100, x_110, x_87);
return x_111;
}
}
}
}
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
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3(obj* x_0, obj* x_1) {
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
obj* l_io_print___at_lean_process__file___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_lean_process__file___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_0, x_1);
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
x_18 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_17, x_14);
return x_18;
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
x_6 = l_io_println___at_lean_process__file___spec__1(x_5, x_2);
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
x_48 = l_io_println___at_lean_process__file___spec__1(x_47, x_2);
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
x_62 = l_io_println___at_lean_process__file___spec__1(x_61, x_2);
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
x_76 = l_io_println___at_lean_process__file___spec__1(x_75, x_2);
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
x_27 = l_io_println___at_lean_process__file___spec__1(x_26, x_12);
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
x_43 = l_io_println___at_lean_process__file___spec__1(x_42, x_12);
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
obj* l___private_init_io_12__put__str___at_lean_process__file___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_lean_process__file___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_print___at_lean_process__file___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_print___at_lean_process__file___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_println___at_lean_process__file___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_println___at_lean_process__file___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
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
 l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1 = _init_l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_run__frontend__aux___main___spec__1___closed__1);
 l_lean_run__frontend__aux___main___closed__1 = _init_l_lean_run__frontend__aux___main___closed__1();
lean::mark_persistent(l_lean_run__frontend__aux___main___closed__1);
 l_lean_run__frontend__aux___main___closed__2 = _init_l_lean_run__frontend__aux___main___closed__2();
lean::mark_persistent(l_lean_run__frontend__aux___main___closed__2);
 l_lean_run__frontend__aux___main___closed__3 = _init_l_lean_run__frontend__aux___main___closed__3();
lean::mark_persistent(l_lean_run__frontend__aux___main___closed__3);
 l_lean_run__frontend__aux___main___closed__4 = _init_l_lean_run__frontend__aux___main___closed__4();
lean::mark_persistent(l_lean_run__frontend__aux___main___closed__4);
 l_lean_run__frontend___closed__1 = _init_l_lean_run__frontend___closed__1();
lean::mark_persistent(l_lean_run__frontend___closed__1);
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

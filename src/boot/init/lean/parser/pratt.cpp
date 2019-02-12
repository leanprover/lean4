// Lean compiler output
// Module: init.lean.parser.pratt
// Imports: init.lean.parser.token
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_lean_parser_monad__parsec_error___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_curr__lbp(obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_pratt__parser(obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_pratt_1__trailing__loop___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__2(obj*, obj*);
extern obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_pratt__parser___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_pratt__parser___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_pratt__parser_tokens___rarg(obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_pratt_1__trailing__loop___main___spec__1(obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_curr__lbp___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_pratt__parser___spec__3(obj*, obj*);
obj* l_lean_parser_pratt__parser_view(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_pratt__parser_tokens(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop(obj*);
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l_lean_parser_pratt__parser___rarg___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_pratt__parser___rarg___lambda__1(obj*, obj*);
extern obj* l_lean_parser_indexed___rarg___closed__1;
obj* l_lean_parser_pratt__parser___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
obj* l_lean_parser_curr__lbp___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_curr__lbp___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l___private_init_lean_parser_rec_1__run__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__3(obj*, obj*);
obj* l_lean_parser_curr__lbp___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__1(obj*, obj*);
obj* l_lean_parser_pratt__parser_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main(obj*);
obj* l_list_append___rarg(obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_lean_parser_pratt__parser___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_pratt__parser___spec__2(obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_pratt__parser___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_6);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_2(x_10, lean::box(0), x_9);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__1___rarg), 7, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_6);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_2(x_10, lean::box(0), x_9);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__2___rarg), 7, 0);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_6);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_2(x_10, lean::box(0), x_9);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__3___rarg), 7, 0);
return x_4;
}
}
obj* l_lean_parser_curr__lbp___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_5 = l_lean_parser_indexed___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::apply_2(x_1, lean::box(0), x_5);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_curr__lbp___rarg___lambda__3), 6, 5);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_2);
lean::closure_set(x_11, 2, x_4);
lean::closure_set(x_11, 3, x_8);
lean::closure_set(x_11, 4, x_3);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_7, x_11);
return x_12;
}
}
obj* _init_l_lean_parser_curr__lbp___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("curr_lbp: unreachable");
return x_0;
}
}
obj* l_lean_parser_curr__lbp___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_4);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__1___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8, x_2);
return x_14;
}
else
{
obj* x_17; obj* x_20; obj* x_23; obj* x_26; 
lean::dec(x_1);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::apply_2(x_3, lean::box(0), x_23);
return x_26;
}
}
}
obj* l_lean_parser_curr__lbp___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::string_mk_iterator(x_0);
x_10 = l_lean_parser_trie_match__prefix___rarg(x_6, x_9);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
lean::inc(x_13);
x_17 = lean::apply_2(x_13, lean::box(0), x_10);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_curr__lbp___rarg___lambda__1), 5, 4);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_2);
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_13);
x_19 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
obj* _init_l_lean_parser_curr__lbp___rarg___lambda__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("string_lit");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_curr__lbp___rarg___lambda__3___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("curr_lbp: unknown token kind");
return x_0;
}
}
obj* l_lean_parser_curr__lbp___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_5, 0);
lean::inc(x_19);
lean::dec(x_5);
switch (lean::obj_tag(x_19)) {
case 0:
{
obj* x_22; obj* x_25; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
lean::inc(x_3);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_curr__lbp___rarg___lambda__2), 6, 5);
lean::closure_set(x_29, 0, x_25);
lean::closure_set(x_29, 1, x_0);
lean::closure_set(x_29, 2, x_1);
lean::closure_set(x_29, 3, x_2);
lean::closure_set(x_29, 4, x_3);
x_30 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_4, x_29);
return x_30;
}
case 1:
{
obj* x_36; obj* x_39; obj* x_42; obj* x_44; 
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
lean::dec(x_0);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_max__prec;
lean::inc(x_42);
x_44 = lean::apply_2(x_39, lean::box(0), x_42);
return x_44;
}
case 2:
{
obj* x_47; obj* x_50; obj* x_53; uint8 x_54; 
lean::dec(x_4);
lean::dec(x_3);
x_47 = lean::cnstr_get(x_19, 0);
lean::inc(x_47);
lean::dec(x_19);
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
lean::dec(x_47);
x_53 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_54 = lean::name_dec_eq(x_50, x_53);
if (x_54 == 0)
{
obj* x_55; uint8 x_56; 
x_55 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
x_56 = lean::name_dec_eq(x_50, x_55);
lean::dec(x_50);
if (x_56 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_65; 
lean::dec(x_0);
x_59 = lean::box(0);
x_60 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_61 = l_mjoin___rarg___closed__1;
lean::inc(x_59);
lean::inc(x_61);
lean::inc(x_60);
x_65 = l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__2___rarg(x_1, lean::box(0), x_60, x_61, x_59, x_59, x_2);
return x_65;
}
else
{
obj* x_68; obj* x_71; obj* x_74; obj* x_76; 
lean::dec(x_1);
lean::dec(x_2);
x_68 = lean::cnstr_get(x_0, 0);
lean::inc(x_68);
lean::dec(x_0);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
x_74 = l_lean_parser_max__prec;
lean::inc(x_74);
x_76 = lean::apply_2(x_71, lean::box(0), x_74);
return x_76;
}
}
else
{
obj* x_80; obj* x_83; obj* x_86; obj* x_88; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_50);
x_80 = lean::cnstr_get(x_0, 0);
lean::inc(x_80);
lean::dec(x_0);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
x_86 = l_lean_parser_max__prec;
lean::inc(x_86);
x_88 = lean::apply_2(x_83, lean::box(0), x_86);
return x_88;
}
}
default:
{
obj* x_93; obj* x_94; obj* x_95; obj* x_99; 
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_93 = lean::box(0);
x_94 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_95 = l_mjoin___rarg___closed__1;
lean::inc(x_93);
lean::inc(x_95);
lean::inc(x_94);
x_99 = l_lean_parser_monad__parsec_error___at_lean_parser_curr__lbp___spec__3___rarg(x_1, lean::box(0), x_94, x_95, x_93, x_93, x_2);
return x_99;
}
}
}
}
}
obj* l_lean_parser_curr__lbp(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_curr__lbp___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_pratt_1__trailing__loop___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_6);
lean::dec(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
lean::closure_set(x_9, 3, x_5);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::apply_2(x_10, lean::box(0), x_9);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_pratt_1__trailing__loop___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_pratt_1__trailing__loop___main___spec__1___rarg), 7, 0);
return x_4;
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::nat_dec_eq(x_6, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_12; obj* x_13; obj* x_16; obj* x_23; obj* x_25; obj* x_26; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_6, x_12);
lean::dec(x_12);
lean::dec(x_6);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::inc(x_8);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_lean_parser_curr__lbp___rarg(x_0, x_1, x_2, x_3, x_8);
lean::inc(x_16);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg___lambda__2), 11, 10);
lean::closure_set(x_25, 0, x_5);
lean::closure_set(x_25, 1, x_0);
lean::closure_set(x_25, 2, x_7);
lean::closure_set(x_25, 3, x_4);
lean::closure_set(x_25, 4, x_8);
lean::closure_set(x_25, 5, x_1);
lean::closure_set(x_25, 6, x_2);
lean::closure_set(x_25, 7, x_3);
lean::closure_set(x_25, 8, x_13);
lean::closure_set(x_25, 9, x_16);
x_26 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_23, x_25);
return x_26;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_40; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_34 = lean::box(0);
x_35 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_36 = l_mjoin___rarg___closed__1;
lean::inc(x_34);
lean::inc(x_36);
lean::inc(x_35);
x_40 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_pratt_1__trailing__loop___main___spec__1___rarg(x_2, lean::box(0), x_35, x_36, x_34, x_34, x_8);
return x_40;
}
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_7);
return x_9;
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9, obj* x_10) {
_start:
{
uint8 x_11; 
x_11 = lean::nat_dec_lt(x_0, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_21; obj* x_24; obj* x_27; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_1, 0);
lean::inc(x_21);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = lean::apply_2(x_24, lean::box(0), x_2);
return x_27;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
lean::inc(x_4);
lean::inc(x_3);
x_30 = lean::apply_2(x_3, x_2, x_4);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg___lambda__1), 9, 8);
lean::closure_set(x_31, 0, x_1);
lean::closure_set(x_31, 1, x_5);
lean::closure_set(x_31, 2, x_6);
lean::closure_set(x_31, 3, x_7);
lean::closure_set(x_31, 4, x_3);
lean::closure_set(x_31, 5, x_0);
lean::closure_set(x_31, 6, x_8);
lean::closure_set(x_31, 7, x_4);
x_32 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_30, x_31);
return x_32;
}
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg), 9, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_pratt_1__trailing__loop___rarg), 9, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_pratt__parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___rarg___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_pratt__parser___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_pratt__parser___spec__2___rarg), 6, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_pratt__parser___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___rarg), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_3);
x_5 = lean::apply_1(x_0, x_4);
return x_5;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_pratt__parser___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run___at_lean_parser_pratt__parser___spec__3___rarg), 4, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::apply_2(x_6, lean::box(0), x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg___lambda__2), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_2);
lean::closure_set(x_11, 3, x_3);
x_12 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_pratt__parser___spec__2___rarg(x_1, lean::box(0), x_6, x_7, x_5, x_5);
return x_11;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_12; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_8);
lean::dec(x_6);
x_12 = l_lean_parser_rec__t_run___at_lean_parser_pratt__parser___spec__3___rarg(x_2, x_5, x_3, x_9);
return x_12;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_pratt__parser___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___rarg___lambda__4), 8, 6);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_6);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_1);
lean::closure_set(x_13, 4, x_3);
lean::closure_set(x_13, 5, x_7);
x_14 = l_lean_parser_rec__t_run__parsec___at_lean_parser_pratt__parser___spec__1___rarg(x_0, x_2, x_8, x_13);
return x_14;
}
}
obj* l_lean_parser_pratt__parser___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_10; 
x_2 = lean::string_iterator_remaining(x_1);
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::apply_2(x_7, lean::box(0), x_2);
return x_10;
}
}
obj* l_lean_parser_pratt__parser___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_13; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_8, x_9);
lean::dec(x_9);
lean::dec(x_8);
x_13 = l___private_init_lean_parser_pratt_1__trailing__loop___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_10, x_6, x_7);
return x_13;
}
}
obj* l_lean_parser_pratt__parser___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_11);
x_13 = lean::apply_2(x_9, lean::box(0), x_11);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___rarg___lambda__1), 2, 1);
lean::closure_set(x_15, 0, x_1);
lean::inc(x_2);
x_17 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_13, x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___rarg___lambda__2), 9, 8);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_3);
lean::closure_set(x_18, 2, x_0);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_6);
lean::closure_set(x_18, 6, x_8);
lean::closure_set(x_18, 7, x_7);
x_19 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
obj* l_lean_parser_pratt__parser___rarg___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::inc(x_7);
x_11 = lean::apply_1(x_1, x_7);
lean::inc(x_8);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___rarg___lambda__3), 9, 8);
lean::closure_set(x_13, 0, x_2);
lean::closure_set(x_13, 1, x_0);
lean::closure_set(x_13, 2, x_8);
lean::closure_set(x_13, 3, x_3);
lean::closure_set(x_13, 4, x_4);
lean::closure_set(x_13, 5, x_5);
lean::closure_set(x_13, 6, x_6);
lean::closure_set(x_13, 7, x_7);
x_14 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_lean_parser_pratt__parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___rarg), 9, 0);
return x_2;
}
}
obj* l_lean_parser_pratt__parser_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_append___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_pratt__parser_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8, obj* x_9) {
_start:
{
obj* x_20; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser_tokens___rarg), 2, 0);
return x_20;
}
}
obj* l_lean_parser_pratt__parser_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_18; obj* x_21; 
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_18 = l_mjoin___rarg___closed__1;
lean::inc(x_18);
lean::inc(x_18);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
obj* l_lean_parser_pratt__parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser_view___rarg), 9, 0);
return x_2;
}
}
void initialize_init_lean_parser_token();
static bool _G_initialized = false;
void initialize_init_lean_parser_pratt() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_token();
 l_lean_parser_curr__lbp___rarg___lambda__1___closed__1 = _init_l_lean_parser_curr__lbp___rarg___lambda__1___closed__1();
 l_lean_parser_curr__lbp___rarg___lambda__3___closed__1 = _init_l_lean_parser_curr__lbp___rarg___lambda__3___closed__1();
 l_lean_parser_curr__lbp___rarg___lambda__3___closed__2 = _init_l_lean_parser_curr__lbp___rarg___lambda__3___closed__2();
}

// Lean compiler output
// Module: init.lean.extern
// Imports: init.lean.expr init.data.option.basic
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
obj* l_list_nth___main___rarg(obj*, obj*);
obj* l_lean_get__extern__entry__for__aux(obj*, obj*);
obj* l_lean_expand__extern__entry(obj*, obj*);
namespace lean {
obj* expand_extern_pattern_core(obj*, obj*);
}
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_list_foldl___main___at_lean_mk__simple__fn__call___spec__1(obj*, obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
namespace lean {
obj* mk_adhoc_ext_entry_core(obj*);
}
namespace lean {
obj* string_length(obj*);
}
namespace lean {
uint32 string_iterator_curr(obj*);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_get__extern__entry__for__aux___main___closed__1;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
extern obj* l_list_repr__aux___main___rarg___closed__1;
namespace lean {
uint8 string_iterator_has_next(obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
obj* mk_std_ext_entry_core(obj*, obj*);
}
extern obj* l_string_join___closed__1;
obj* l_lean_get__extern__entry__for__aux___main(obj*, obj*);
namespace lean {
obj* mk_inline_ext_entry_core(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_expand__extern__pattern__aux___main(obj*, obj*, obj*, obj*);
namespace lean {
obj* mk_extern_call_core(obj*, obj*, obj*);
}
obj* l_list_intersperse___main___rarg(obj*, obj*);
obj* l_lean_extern__entry_backend(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_expand__extern__pattern__aux(obj*, obj*, obj*, obj*);
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_lean_extern__entry_backend___main(obj*);
namespace lean {
obj* string_mk_iterator(obj*);
}
namespace lean {
obj* mk_foreign_ext_entry_core(obj*, obj*);
}
namespace lean {
obj* mk_extern_attr_data_core(obj*, obj*);
}
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_lean_expand__extern__entry___main(obj*, obj*);
obj* l_lean_mk__simple__fn__call(obj*, obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_option_has__repr___rarg___closed__3;
namespace lean {
obj* string_push(obj*, uint32);
}
namespace lean {
obj* get_extern_entry_for_core(obj*, obj*);
}
namespace lean {
obj* mk_adhoc_ext_entry_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
}
namespace lean {
obj* mk_inline_ext_entry_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_std_ext_entry_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_foreign_ext_entry_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
namespace lean {
obj* mk_extern_attr_data_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}
obj* l_lean_expand__extern__pattern__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_10; uint8 x_12; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_1);
x_12 = lean::string_iterator_has_next(x_2);
if (x_12 == 0)
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_17; 
x_17 = lean::box(0);
x_10 = x_17;
goto lbl_11;
}
lbl_11:
{
uint32 x_19; uint32 x_20; uint8 x_21; 
lean::dec(x_10);
x_19 = lean::string_iterator_curr(x_2);
x_20 = 35;
x_21 = x_19 == x_20;
if (x_21 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_7);
x_23 = lean::string_iterator_next(x_2);
x_24 = lean::string_push(x_3, x_19);
x_1 = x_8;
x_2 = x_23;
x_3 = x_24;
goto _start;
}
else
{
obj* x_26; uint32 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; 
x_26 = lean::string_iterator_next(x_2);
x_27 = lean::string_iterator_curr(x_26);
x_28 = lean::uint32_to_nat(x_27);
x_29 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_30 = lean::nat_sub(x_28, x_29);
lean::dec(x_28);
x_32 = lean::nat_sub(x_30, x_7);
lean::dec(x_7);
lean::dec(x_30);
x_35 = lean::string_iterator_next(x_26);
lean::inc(x_0);
x_37 = l_list_nth___main___rarg(x_0, x_32);
x_38 = l_string_join___closed__1;
lean::inc(x_38);
x_40 = l_option_get__or__else___main___rarg(x_37, x_38);
x_41 = lean::string_append(x_3, x_40);
lean::dec(x_40);
x_1 = x_8;
x_2 = x_35;
x_3 = x_41;
goto _start;
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l_lean_expand__extern__pattern__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_expand__extern__pattern__aux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
namespace lean {
obj* expand_extern_pattern_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_2 = lean::string_length(x_0);
x_3 = lean::string_mk_iterator(x_0);
x_4 = l_string_join___closed__1;
lean::inc(x_4);
x_6 = l_lean_expand__extern__pattern__aux___main(x_1, x_2, x_3, x_4);
return x_6;
}
}
}
obj* l_list_foldl___main___at_lean_mk__simple__fn__call___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::string_append(x_0, x_2);
lean::dec(x_2);
x_0 = x_7;
x_1 = x_4;
goto _start;
}
}
}
obj* l_lean_mk__simple__fn__call(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
x_2 = l_prod_has__repr___rarg___closed__1;
x_3 = lean::string_append(x_0, x_2);
x_4 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_4);
x_6 = l_list_intersperse___main___rarg(x_4, x_1);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = l_list_foldl___main___at_lean_mk__simple__fn__call___spec__1(x_7, x_6);
x_10 = lean::string_append(x_3, x_9);
lean::dec(x_9);
x_12 = l_option_has__repr___rarg___closed__3;
x_13 = lean::string_append(x_10, x_12);
return x_13;
}
}
obj* l_lean_expand__extern__entry___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::expand_extern_pattern_core(x_5, x_1);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
default:
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_lean_mk__simple__fn__call(x_10, x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
}
}
}
obj* l_lean_expand__extern__entry(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_expand__extern__entry___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_extern__entry_backend___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_extern__entry_backend(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_extern__entry_backend___main(x_0);
return x_1;
}
}
obj* _init_l_lean_get__extern__entry__for__aux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("all");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_get__extern__entry__for__aux___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_10; obj* x_11; uint8 x_12; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_4);
x_10 = l_lean_extern__entry_backend___main(x_4);
x_11 = l_lean_get__extern__entry__for__aux___main___closed__1;
x_12 = lean_name_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = lean_name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_13 == 0)
{
lean::dec(x_4);
x_1 = x_6;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_6);
lean::dec(x_0);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_4);
return x_19;
}
}
else
{
obj* x_23; 
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_0);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_4);
return x_23;
}
}
}
}
obj* l_lean_get__extern__entry__for__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_get__extern__entry__for__aux___main(x_0, x_1);
return x_2;
}
}
namespace lean {
obj* get_extern_entry_for_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_get__extern__entry__for__aux___main(x_1, x_2);
return x_5;
}
}
}
namespace lean {
obj* mk_extern_call_core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::get_extern_entry_for_core(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_expand__extern__entry___main(x_6, x_2);
return x_9;
}
}
}
}
void initialize_init_lean_expr();
void initialize_init_data_option_basic();
static bool _G_initialized = false;
void initialize_init_lean_extern() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_expr();
 initialize_init_data_option_basic();
 l_lean_get__extern__entry__for__aux___main___closed__1 = _init_l_lean_get__extern__entry__for__aux___main___closed__1();
}

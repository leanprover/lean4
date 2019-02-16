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
obj* x_7; obj* x_8; obj* x_10; obj* x_12; uint8 x_14; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::dec(x_1);
x_14 = lean::string_iterator_has_next(x_2);
if (x_14 == 0)
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_19; 
x_19 = lean::box(0);
x_12 = x_19;
goto lbl_13;
}
lbl_11:
{
obj* x_21; uint32 x_22; obj* x_23; uint32 x_24; uint32 x_25; uint8 x_26; obj* x_27; uint32 x_28; 
lean::dec(x_10);
x_21 = lean::string_iterator_next(x_2);
x_22 = lean::string_iterator_curr(x_21);
x_23 = lean::uint32_to_nat(x_22);
x_24 = 48;
x_25 = 55296;
x_26 = x_24 < x_25;
x_27 = lean::string_iterator_next(x_21);
if (x_26 == 0)
{
uint32 x_30; uint8 x_31; 
x_30 = 57343;
x_31 = x_30 < x_24;
if (x_31 == 0)
{
uint32 x_32; 
x_32 = 0;
x_28 = x_32;
goto lbl_29;
}
else
{
uint32 x_33; uint8 x_34; 
x_33 = 1114112;
x_34 = x_24 < x_33;
if (x_34 == 0)
{
uint32 x_35; 
x_35 = 0;
x_28 = x_35;
goto lbl_29;
}
else
{
x_28 = x_24;
goto lbl_29;
}
}
}
else
{
x_28 = x_24;
goto lbl_29;
}
lbl_29:
{
obj* x_36; obj* x_37; obj* x_40; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_36 = lean::uint32_to_nat(x_28);
x_37 = lean::nat_sub(x_23, x_36);
lean::dec(x_36);
lean::dec(x_23);
x_40 = lean::nat_sub(x_37, x_7);
lean::dec(x_7);
lean::dec(x_37);
lean::inc(x_0);
x_44 = l_list_nth___main___rarg(x_0, x_40);
x_45 = l_string_join___closed__1;
lean::inc(x_45);
x_47 = l_option_get__or__else___main___rarg(x_44, x_45);
x_48 = lean::string_append(x_3, x_47);
lean::dec(x_47);
x_1 = x_8;
x_2 = x_27;
x_3 = x_48;
goto _start;
}
}
lbl_13:
{
uint32 x_52; uint32 x_53; uint32 x_54; uint8 x_55; uint32 x_56; 
lean::dec(x_12);
x_52 = lean::string_iterator_curr(x_2);
x_53 = 35;
x_54 = 55296;
x_55 = x_53 < x_54;
if (x_55 == 0)
{
uint32 x_58; uint8 x_59; 
x_58 = 57343;
x_59 = x_58 < x_53;
if (x_59 == 0)
{
uint32 x_60; 
x_60 = 0;
x_56 = x_60;
goto lbl_57;
}
else
{
uint32 x_61; uint8 x_62; 
x_61 = 1114112;
x_62 = x_53 < x_61;
if (x_62 == 0)
{
uint32 x_63; 
x_63 = 0;
x_56 = x_63;
goto lbl_57;
}
else
{
x_56 = x_53;
goto lbl_57;
}
}
}
else
{
x_56 = x_53;
goto lbl_57;
}
lbl_57:
{
uint8 x_64; 
x_64 = x_52 == x_56;
if (x_64 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_7);
x_66 = lean::string_iterator_next(x_2);
x_67 = lean::string_push(x_3, x_52);
x_1 = x_8;
x_2 = x_66;
x_3 = x_67;
goto _start;
}
else
{
obj* x_69; 
x_69 = lean::box(0);
x_10 = x_69;
goto lbl_11;
}
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
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::string_append(x_0, x_3);
lean::dec(x_3);
x_0 = x_8;
x_1 = x_5;
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
case 2:
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
default:
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_lean_mk__simple__fn__call(x_15, x_1);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
lean::inc(x_5);
x_11 = l_lean_extern__entry_backend___main(x_5);
x_12 = l_lean_get__extern__entry__for__aux___main___closed__1;
x_13 = lean_name_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = lean_name_dec_eq(x_11, x_0);
lean::dec(x_11);
if (x_14 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_20; 
lean::dec(x_7);
lean::dec(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_5);
return x_20;
}
}
else
{
obj* x_24; 
lean::dec(x_11);
lean::dec(x_7);
lean::dec(x_0);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_5);
return x_24;
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
obj* x_6; 
lean::dec(x_3);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_10 = l_lean_expand__extern__entry___main(x_7, x_2);
return x_10;
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

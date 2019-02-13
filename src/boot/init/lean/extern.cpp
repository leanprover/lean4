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
uint8 nat_dec_lt(obj*, obj*);
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
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; uint8 x_13; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_13 = lean::string_iterator_has_next(x_2);
if (x_13 == 0)
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_19; 
x_19 = lean::box(0);
x_11 = x_19;
goto lbl_12;
}
lbl_10:
{
obj* x_21; uint32 x_22; obj* x_23; obj* x_24; uint8 x_25; obj* x_27; uint32 x_28; 
lean::dec(x_9);
x_21 = lean::string_iterator_next(x_2);
x_22 = lean::string_iterator_curr(x_21);
x_23 = lean::mk_nat_obj(48u);
x_24 = lean::mk_nat_obj(55296u);
x_25 = lean::nat_dec_lt(x_23, x_24);
lean::dec(x_24);
x_27 = lean::string_iterator_next(x_21);
if (x_25 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::mk_nat_obj(57343u);
x_31 = lean::nat_dec_lt(x_30, x_23);
lean::dec(x_30);
if (x_31 == 0)
{
uint32 x_34; 
lean::dec(x_23);
x_34 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_28 = x_34;
goto lbl_29;
}
else
{
obj* x_36; uint8 x_37; 
x_36 = lean::mk_nat_obj(1114112u);
x_37 = lean::nat_dec_lt(x_23, x_36);
lean::dec(x_36);
if (x_37 == 0)
{
uint32 x_40; 
lean::dec(x_23);
x_40 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_28 = x_40;
goto lbl_29;
}
else
{
uint32 x_43; 
lean::dec(x_4);
x_43 = lean::unbox_uint32(x_23);
lean::dec(x_23);
x_28 = x_43;
goto lbl_29;
}
}
}
else
{
uint32 x_46; 
lean::dec(x_4);
x_46 = lean::unbox_uint32(x_23);
lean::dec(x_23);
x_28 = x_46;
goto lbl_29;
}
lbl_29:
{
obj* x_48; obj* x_49; obj* x_50; obj* x_53; obj* x_57; obj* x_58; obj* x_60; obj* x_61; 
x_48 = lean::box_uint32(x_22);
x_49 = lean::box_uint32(x_28);
x_50 = lean::nat_sub(x_48, x_49);
lean::dec(x_49);
lean::dec(x_48);
x_53 = lean::nat_sub(x_50, x_6);
lean::dec(x_6);
lean::dec(x_50);
lean::inc(x_0);
x_57 = l_list_nth___main___rarg(x_0, x_53);
x_58 = l_string_join___closed__1;
lean::inc(x_58);
x_60 = l_option_get__or__else___main___rarg(x_57, x_58);
x_61 = lean::string_append(x_3, x_60);
lean::dec(x_60);
x_1 = x_7;
x_2 = x_27;
x_3 = x_61;
goto _start;
}
}
lbl_12:
{
uint32 x_65; obj* x_66; obj* x_67; uint8 x_68; uint32 x_70; 
lean::dec(x_11);
x_65 = lean::string_iterator_curr(x_2);
x_66 = lean::mk_nat_obj(35u);
x_67 = lean::mk_nat_obj(55296u);
x_68 = lean::nat_dec_lt(x_66, x_67);
lean::dec(x_67);
if (x_68 == 0)
{
obj* x_72; uint8 x_73; 
x_72 = lean::mk_nat_obj(57343u);
x_73 = lean::nat_dec_lt(x_72, x_66);
lean::dec(x_72);
if (x_73 == 0)
{
uint32 x_76; 
lean::dec(x_66);
x_76 = lean::unbox_uint32(x_4);
x_70 = x_76;
goto lbl_71;
}
else
{
obj* x_77; uint8 x_78; 
x_77 = lean::mk_nat_obj(1114112u);
x_78 = lean::nat_dec_lt(x_66, x_77);
lean::dec(x_77);
if (x_78 == 0)
{
uint32 x_81; 
lean::dec(x_66);
x_81 = lean::unbox_uint32(x_4);
x_70 = x_81;
goto lbl_71;
}
else
{
uint32 x_82; 
x_82 = lean::unbox_uint32(x_66);
lean::dec(x_66);
x_70 = x_82;
goto lbl_71;
}
}
}
else
{
uint32 x_84; 
x_84 = lean::unbox_uint32(x_66);
lean::dec(x_66);
x_70 = x_84;
goto lbl_71;
}
lbl_71:
{
obj* x_86; obj* x_87; uint8 x_88; 
x_86 = lean::box_uint32(x_65);
x_87 = lean::box_uint32(x_70);
x_88 = lean::nat_dec_eq(x_86, x_87);
lean::dec(x_87);
lean::dec(x_86);
if (x_88 == 0)
{
obj* x_93; obj* x_94; 
lean::dec(x_4);
lean::dec(x_6);
x_93 = lean::string_iterator_next(x_2);
x_94 = lean::string_push(x_3, x_65);
x_1 = x_7;
x_2 = x_93;
x_3 = x_94;
goto _start;
}
else
{
obj* x_96; 
x_96 = lean::box(0);
x_9 = x_96;
goto lbl_10;
}
}
}
}
else
{
lean::dec(x_4);
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

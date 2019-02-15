// Lean compiler output
// Module: init.lean.compiler.const_folding
// Imports: init.lean.expr init.platform init.data.rbmap.default
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
namespace lean {
obj* fold_bin_op_core(uint8, obj*, obj*, obj*);
}
obj* l_nat_mod___boxed(obj*, obj*);
obj* l_lean_const__folding_find__bin__fold__fn(obj*);
obj* l_lean_const__folding_bin__fold__fns;
obj* l_lean_const__folding_fold__nat__add___rarg___closed__1;
obj* l_lean_const__folding_fold__nat__mul(uint8);
namespace lean {
obj* get_num_lit_core(obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_const__folding_mk__uint__type__name(obj*);
obj* l_lean_const__folding_fold__nat__div___rarg___closed__1;
obj* l_lean_const__folding_fold__uint__sub___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_const__folding_fold__nat__div___boxed(obj*);
obj* l_nat_mul___boxed(obj*, obj*);
obj* l_lean_const__folding_fold__uint__mod___closed__1;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_lean_const__folding_fold__uint__mod___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_const__folding_get__info__from__fn___main(obj*, obj*);
obj* l_lean_const__folding_fold__bin__nat(obj*, obj*, obj*);
obj* l_lean_const__folding_fold__uint__mul(uint8, obj*, obj*);
obj* l_lean_const__folding_fold__uint__mul___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_const__folding_fold__nat__mod___rarg(obj*, obj*);
extern obj* l_system_platform_nbits;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_const__folding_fold__uint__sub___closed__1;
obj* l_list_map___main___at_lean_const__folding_uint__bin__fold__fns___spec__1(obj*, obj*);
obj* l_lean_const__folding_fold__uint__sub___boxed(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_lean_const__folding_fold__uint__mod___boxed(obj*, obj*, obj*);
obj* l_nat_add___boxed(obj*, obj*);
obj* l_lean_const__folding_mk__uint__type__name___closed__1;
obj* l_lean_const__folding_fold__bin__uint(obj*, uint8, obj*, obj*);
obj* l_lean_const__folding_fold__uint__add___boxed(obj*, obj*, obj*);
obj* l_lean_const__folding_fold__nat__div___rarg(obj*, obj*);
obj* l_lean_const__folding_fold__uint__div(uint8, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_lean_const__folding_fold__bin__uint___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_const__folding_fold__uint__sub(uint8, obj*, obj*);
obj* l_lean_const__folding_fold__uint__add(uint8, obj*, obj*);
obj* l_lean_const__folding_uint__bin__fold__fns;
obj* l_lean_const__folding_fold__nat__add(uint8);
obj* l_lean_const__folding_get__info__from__val___main(obj*);
obj* l_lean_const__folding_fold__nat__mod(uint8);
obj* l_lean_const__folding_fold__uint__sub___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_const__folding_get__info__from__val(obj*);
obj* l_lean_const__folding_fold__uint__div___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_const__folding_fold__uint__mul___boxed(obj*, obj*, obj*);
obj* l_lean_const__folding_fold__uint__add___closed__1;
obj* l_lean_const__folding_fold__nat__mul___rarg(obj*, obj*);
obj* l_lean_name_append___main(obj*, obj*);
obj* l_list_foldl___main___at_lean_const__folding_uint__bin__fold__fns___spec__2(obj*, obj*);
obj* l_lean_const__folding_find__bin__fold__fn__aux(obj*, obj*);
obj* l_lean_const__folding_find__bin__fold__fn__aux___main(obj*, obj*);
obj* l_lean_const__folding_fold__uint__mod(uint8, obj*, obj*);
obj* l_lean_const__folding_get__info__from__fn(obj*, obj*);
obj* l_lean_const__folding_bin__fold__fn;
obj* l_lean_const__folding_fold__uint__div___closed__1;
obj* l_lean_const__folding_pre__uint__bin__fold__fns;
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_lean_const__folding_fold__nat__div(uint8);
obj* l_lean_const__folding_fold__uint__mod___lambda__1(obj*, uint8, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_const__folding_fold__uint__div___boxed(obj*, obj*, obj*);
obj* l_nat_pow___main(obj*, obj*);
obj* l_lean_const__folding_fold__uint__div___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_const__folding_fold__bin__op___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_const__folding_mk__uint__lit(obj*, obj*);
obj* l_lean_const__folding_fold__uint__mul___closed__1;
obj* l_lean_const__folding_fold__nat__add___boxed(obj*);
obj* l_lean_const__folding_fold__nat__mul___boxed(obj*);
obj* l_lean_const__folding_fold__nat__mul___rarg___closed__1;
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_lean_const__folding_fold__uint__add___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_nat_repr(obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_lean_const__folding_get__num__lit___main(obj*);
obj* l_lean_const__folding_fold__uint__add___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_const__folding_is__of__nat(obj*);
obj* l_list_foldr___main___at_lean_const__folding_is__of__nat___spec__1(obj*, obj*);
obj* l_lean_const__folding_fold__nat__add___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_const__folding_fold__uint__mul___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_const__folding_num__scalar__types;
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_const__folding_fold__nat__mod___rarg___closed__1;
obj* l_nat_div___boxed(obj*, obj*);
obj* l_lean_const__folding_fold__nat__mod___boxed(obj*);
obj* _init_l_lean_const__folding_bin__fold__fn() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_const__folding_mk__uint__type__name___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uint");
return x_0;
}
}
obj* l_lean_const__folding_mk__uint__type__name(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_1 = l_nat_repr(x_0);
x_2 = l_lean_const__folding_mk__uint__type__name___closed__1;
lean::inc(x_2);
x_4 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean_name_mk_string(x_6, x_4);
return x_7;
}
}
obj* _init_l_lean_const__folding_num__scalar__types() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_0 = lean::mk_nat_obj(8u);
lean::inc(x_0);
x_2 = l_lean_const__folding_mk__uint__type__name(x_0);
x_3 = lean::mk_string("of_nat");
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean_name_mk_string(x_2, x_3);
x_7 = lean::mk_nat_obj(2u);
lean::inc(x_0);
lean::inc(x_7);
x_10 = l_nat_pow___main(x_7, x_0);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_2);
lean::cnstr_set(x_11, 2, x_6);
lean::cnstr_set(x_11, 3, x_10);
x_12 = lean::mk_nat_obj(16u);
lean::inc(x_12);
x_14 = l_lean_const__folding_mk__uint__type__name(x_12);
lean::inc(x_3);
lean::inc(x_14);
x_17 = lean_name_mk_string(x_14, x_3);
lean::inc(x_12);
lean::inc(x_7);
x_20 = l_nat_pow___main(x_7, x_12);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_12);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_17);
lean::cnstr_set(x_21, 3, x_20);
x_22 = lean::mk_nat_obj(32u);
lean::inc(x_22);
x_24 = l_lean_const__folding_mk__uint__type__name(x_22);
lean::inc(x_3);
lean::inc(x_24);
x_27 = lean_name_mk_string(x_24, x_3);
lean::inc(x_22);
lean::inc(x_7);
x_30 = l_nat_pow___main(x_7, x_22);
x_31 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_31, 0, x_22);
lean::cnstr_set(x_31, 1, x_24);
lean::cnstr_set(x_31, 2, x_27);
lean::cnstr_set(x_31, 3, x_30);
x_32 = lean::mk_nat_obj(64u);
lean::inc(x_32);
x_34 = l_lean_const__folding_mk__uint__type__name(x_32);
lean::inc(x_3);
lean::inc(x_34);
x_37 = lean_name_mk_string(x_34, x_3);
lean::inc(x_32);
lean::inc(x_7);
x_40 = l_nat_pow___main(x_7, x_32);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_32);
lean::cnstr_set(x_41, 1, x_34);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_40);
x_42 = lean::box(0);
x_43 = lean::mk_string("usize");
lean::inc(x_42);
x_45 = lean_name_mk_string(x_42, x_43);
lean::inc(x_45);
x_47 = lean_name_mk_string(x_45, x_3);
x_48 = l_system_platform_nbits;
lean::inc(x_48);
x_50 = l_nat_pow___main(x_7, x_48);
lean::inc(x_48);
x_52 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_52, 0, x_48);
lean::cnstr_set(x_52, 1, x_45);
lean::cnstr_set(x_52, 2, x_47);
lean::cnstr_set(x_52, 3, x_50);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_42);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_41);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_31);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_21);
lean::cnstr_set(x_56, 1, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_11);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
}
obj* l_list_foldr___main___at_lean_const__folding_is__of__nat___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; uint8 x_14; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean_name_dec_eq(x_11, x_0);
lean::dec(x_11);
if (x_14 == 0)
{
x_1 = x_8;
goto _start;
}
else
{
uint8 x_19; obj* x_20; 
lean::dec(x_8);
lean::dec(x_0);
x_19 = 1;
x_20 = lean::box(x_19);
return x_20;
}
}
}
}
obj* l_lean_const__folding_is__of__nat(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_const__folding_num__scalar__types;
lean::inc(x_1);
x_3 = l_list_foldr___main___at_lean_const__folding_is__of__nat___spec__1(x_0, x_1);
return x_3;
}
}
obj* l_lean_const__folding_get__info__from__fn___main(obj* x_0, obj* x_1) {
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
obj* x_5; obj* x_7; obj* x_10; uint8 x_12; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
x_12 = lean_name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_12 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_7);
lean::dec(x_0);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_5);
return x_18;
}
}
}
}
obj* l_lean_const__folding_get__info__from__fn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_const__folding_get__info__from__fn___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_const__folding_get__info__from__val___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 2:
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
case 3:
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
}
case 4:
{
obj* x_10; 
lean::dec(x_0);
x_10 = lean::box(0);
return x_10;
}
case 5:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_15; 
lean::dec(x_11);
x_15 = lean::box(0);
return x_15;
}
case 1:
{
obj* x_17; 
lean::dec(x_11);
x_17 = lean::box(0);
return x_17;
}
case 2:
{
obj* x_19; 
lean::dec(x_11);
x_19 = lean::box(0);
return x_19;
}
case 3:
{
obj* x_21; 
lean::dec(x_11);
x_21 = lean::box(0);
return x_21;
}
case 4:
{
obj* x_22; obj* x_25; obj* x_27; 
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_const__folding_num__scalar__types;
lean::inc(x_25);
x_27 = l_lean_const__folding_get__info__from__fn___main(x_22, x_25);
return x_27;
}
case 5:
{
obj* x_29; 
lean::dec(x_11);
x_29 = lean::box(0);
return x_29;
}
case 6:
{
obj* x_31; 
lean::dec(x_11);
x_31 = lean::box(0);
return x_31;
}
case 7:
{
obj* x_33; 
lean::dec(x_11);
x_33 = lean::box(0);
return x_33;
}
case 8:
{
obj* x_35; 
lean::dec(x_11);
x_35 = lean::box(0);
return x_35;
}
case 9:
{
obj* x_37; 
lean::dec(x_11);
x_37 = lean::box(0);
return x_37;
}
case 10:
{
obj* x_39; 
lean::dec(x_11);
x_39 = lean::box(0);
return x_39;
}
default:
{
obj* x_41; 
lean::dec(x_11);
x_41 = lean::box(0);
return x_41;
}
}
}
case 6:
{
obj* x_43; 
lean::dec(x_0);
x_43 = lean::box(0);
return x_43;
}
case 7:
{
obj* x_45; 
lean::dec(x_0);
x_45 = lean::box(0);
return x_45;
}
case 8:
{
obj* x_47; 
lean::dec(x_0);
x_47 = lean::box(0);
return x_47;
}
case 9:
{
obj* x_49; 
lean::dec(x_0);
x_49 = lean::box(0);
return x_49;
}
case 10:
{
obj* x_51; 
lean::dec(x_0);
x_51 = lean::box(0);
return x_51;
}
default:
{
obj* x_53; 
lean::dec(x_0);
x_53 = lean::box(0);
return x_53;
}
}
}
}
obj* l_lean_const__folding_get__info__from__val(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_const__folding_get__info__from__val___main(x_0);
return x_1;
}
}
obj* l_lean_const__folding_get__num__lit___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 2:
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
case 3:
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
}
case 4:
{
obj* x_10; 
lean::dec(x_0);
x_10 = lean::box(0);
return x_10;
}
case 5:
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
lean::dec(x_0);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_18; 
lean::dec(x_13);
lean::dec(x_11);
x_18 = lean::box(0);
return x_18;
}
case 1:
{
obj* x_21; 
lean::dec(x_13);
lean::dec(x_11);
x_21 = lean::box(0);
return x_21;
}
case 2:
{
obj* x_24; 
lean::dec(x_13);
lean::dec(x_11);
x_24 = lean::box(0);
return x_24;
}
case 3:
{
obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
x_27 = lean::box(0);
return x_27;
}
case 4:
{
obj* x_28; obj* x_31; obj* x_33; uint8 x_34; 
x_28 = lean::cnstr_get(x_11, 0);
lean::inc(x_28);
lean::dec(x_11);
x_31 = l_lean_const__folding_num__scalar__types;
lean::inc(x_31);
x_33 = l_list_foldr___main___at_lean_const__folding_is__of__nat___spec__1(x_28, x_31);
x_34 = lean::unbox(x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_37; 
lean::dec(x_13);
x_37 = lean::box(0);
return x_37;
}
else
{
x_0 = x_13;
goto _start;
}
}
case 5:
{
obj* x_41; 
lean::dec(x_13);
lean::dec(x_11);
x_41 = lean::box(0);
return x_41;
}
case 6:
{
obj* x_44; 
lean::dec(x_13);
lean::dec(x_11);
x_44 = lean::box(0);
return x_44;
}
case 7:
{
obj* x_47; 
lean::dec(x_13);
lean::dec(x_11);
x_47 = lean::box(0);
return x_47;
}
case 8:
{
obj* x_50; 
lean::dec(x_13);
lean::dec(x_11);
x_50 = lean::box(0);
return x_50;
}
case 9:
{
obj* x_53; 
lean::dec(x_13);
lean::dec(x_11);
x_53 = lean::box(0);
return x_53;
}
case 10:
{
obj* x_56; 
lean::dec(x_13);
lean::dec(x_11);
x_56 = lean::box(0);
return x_56;
}
default:
{
obj* x_59; 
lean::dec(x_13);
lean::dec(x_11);
x_59 = lean::box(0);
return x_59;
}
}
}
case 6:
{
obj* x_61; 
lean::dec(x_0);
x_61 = lean::box(0);
return x_61;
}
case 7:
{
obj* x_63; 
lean::dec(x_0);
x_63 = lean::box(0);
return x_63;
}
case 8:
{
obj* x_65; 
lean::dec(x_0);
x_65 = lean::box(0);
return x_65;
}
case 9:
{
obj* x_66; 
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
lean::dec(x_0);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; obj* x_72; 
x_69 = lean::cnstr_get(x_66, 0);
lean::inc(x_69);
lean::dec(x_66);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_69);
return x_72;
}
else
{
obj* x_74; 
lean::dec(x_66);
x_74 = lean::box(0);
return x_74;
}
}
case 10:
{
obj* x_76; 
lean::dec(x_0);
x_76 = lean::box(0);
return x_76;
}
default:
{
obj* x_78; 
lean::dec(x_0);
x_78 = lean::box(0);
return x_78;
}
}
}
}
namespace lean {
obj* get_num_lit_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_const__folding_get__num__lit___main(x_0);
return x_1;
}
}
}
obj* l_lean_const__folding_mk__uint__lit(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
x_4 = lean::box(0);
x_5 = lean_expr_mk_const(x_2, x_4);
x_6 = lean::cnstr_get(x_0, 3);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::nat_mod(x_1, x_6);
lean::dec(x_6);
lean::dec(x_1);
x_12 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean_expr_mk_lit(x_12);
x_14 = lean_expr_mk_app(x_5, x_13);
return x_14;
}
}
obj* l_lean_const__folding_fold__bin__uint(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_lean_const__folding_get__num__lit___main(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
}
x_14 = l_lean_const__folding_get__num__lit___main(x_3);
if (lean::obj_tag(x_14) == 0)
{
obj* x_20; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_2);
x_20 = lean::box(0);
return x_20;
}
else
{
obj* x_21; obj* x_24; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
lean::dec(x_14);
x_24 = l_lean_const__folding_get__info__from__val___main(x_2);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; 
lean::dec(x_24);
lean::dec(x_21);
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_0);
x_30 = lean::box(0);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
x_34 = lean::box(x_1);
lean::inc(x_31);
x_36 = lean::apply_4(x_0, x_31, x_34, x_11, x_21);
x_37 = l_lean_const__folding_mk__uint__lit(x_31, x_36);
if (lean::is_scalar(x_13)) {
 x_38 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_38 = x_13;
}
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
}
}
}
}
obj* l_lean_const__folding_fold__bin__uint___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_const__folding_fold__bin__uint(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_const__folding_fold__uint__add___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__add___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__uint__add(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_const__folding_fold__uint__add___closed__1;
lean::inc(x_3);
x_5 = l_lean_const__folding_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__add___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::nat_add(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__add___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_const__folding_fold__uint__add(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_const__folding_fold__uint__add___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_const__folding_fold__uint__add___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_const__folding_fold__uint__mul___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__mul___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__uint__mul(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_const__folding_fold__uint__mul___closed__1;
lean::inc(x_3);
x_5 = l_lean_const__folding_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__mul___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::nat_mul(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__mul___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_const__folding_fold__uint__mul(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_const__folding_fold__uint__mul___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_const__folding_fold__uint__mul___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_const__folding_fold__uint__div___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__div___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__uint__div(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_const__folding_fold__uint__div___closed__1;
lean::inc(x_3);
x_5 = l_lean_const__folding_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__div___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::nat_div(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__div___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_const__folding_fold__uint__div(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_const__folding_fold__uint__div___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_const__folding_fold__uint__div___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_const__folding_fold__uint__mod___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__mod___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__uint__mod(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_const__folding_fold__uint__mod___closed__1;
lean::inc(x_3);
x_5 = l_lean_const__folding_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__mod___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::nat_mod(x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__mod___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_const__folding_fold__uint__mod(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_const__folding_fold__uint__mod___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_const__folding_fold__uint__mod___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_const__folding_fold__uint__sub___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__sub___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__uint__sub(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_const__folding_fold__uint__sub___closed__1;
lean::inc(x_3);
x_5 = l_lean_const__folding_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_const__folding_fold__uint__sub___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 3);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::nat_sub(x_4, x_3);
lean::dec(x_3);
lean::dec(x_4);
x_10 = lean::nat_add(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
return x_10;
}
}
obj* l_lean_const__folding_fold__uint__sub___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_const__folding_fold__uint__sub(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_const__folding_fold__uint__sub___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_const__folding_fold__uint__sub___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_const__folding_pre__uint__bin__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_0 = lean::box(0);
x_1 = lean::mk_string("add");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__add___boxed), 3, 0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::mk_string("mul");
lean::inc(x_0);
x_8 = lean_name_mk_string(x_0, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__mul___boxed), 3, 0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::mk_string("div");
lean::inc(x_0);
x_13 = lean_name_mk_string(x_0, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__div___boxed), 3, 0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::mk_string("mod");
lean::inc(x_0);
x_18 = lean_name_mk_string(x_0, x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__mod___boxed), 3, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::mk_string("sub");
lean::inc(x_0);
x_23 = lean_name_mk_string(x_0, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__uint__sub___boxed), 3, 0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_0);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_20);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_10);
lean::cnstr_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
obj* l_list_map___main___at_lean_const__folding_uint__bin__fold__fns___spec__1(obj* x_0, obj* x_1) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_9 = x_1;
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_14 = x_5;
}
lean::inc(x_0);
x_16 = l_list_map___main___at_lean_const__folding_uint__bin__fold__fns___spec__1(x_0, x_7);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
lean::dec(x_0);
x_20 = l_lean_name_append___main(x_17, x_10);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_12);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_16);
return x_22;
}
}
}
obj* l_list_foldl___main___at_lean_const__folding_uint__bin__fold__fns___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = l_lean_const__folding_pre__uint__bin__fold__fns;
lean::inc(x_8);
x_10 = l_list_map___main___at_lean_const__folding_uint__bin__fold__fns___spec__1(x_3, x_8);
x_11 = l_list_append___rarg(x_0, x_10);
x_0 = x_11;
x_1 = x_5;
goto _start;
}
}
}
obj* _init_l_lean_const__folding_uint__bin__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_const__folding_num__scalar__types;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_lean_const__folding_uint__bin__fold__fns___spec__2(x_0, x_1);
return x_3;
}
}
obj* l_lean_const__folding_fold__bin__nat(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_const__folding_get__num__lit___main(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
}
x_11 = l_lean_const__folding_get__num__lit___main(x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; 
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_0);
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
lean::dec(x_11);
x_20 = lean::apply_2(x_0, x_8, x_17);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean_expr_mk_lit(x_21);
if (lean::is_scalar(x_10)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_10;
}
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
}
}
obj* _init_l_lean_const__folding_fold__nat__add___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_add___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__nat__add___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_const__folding_fold__nat__add___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_const__folding_fold__bin__nat(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_const__folding_fold__nat__add(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__add___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_const__folding_fold__nat__add___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_const__folding_fold__nat__add(x_1);
return x_2;
}
}
obj* _init_l_lean_const__folding_fold__nat__mul___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__nat__mul___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_const__folding_fold__nat__mul___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_const__folding_fold__bin__nat(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_const__folding_fold__nat__mul(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__mul___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_const__folding_fold__nat__mul___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_const__folding_fold__nat__mul(x_1);
return x_2;
}
}
obj* _init_l_lean_const__folding_fold__nat__div___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_div___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__nat__div___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_const__folding_fold__nat__div___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_const__folding_fold__bin__nat(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_const__folding_fold__nat__div(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__div___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_const__folding_fold__nat__div___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_const__folding_fold__nat__div(x_1);
return x_2;
}
}
obj* _init_l_lean_const__folding_fold__nat__mod___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_mod___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_const__folding_fold__nat__mod___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_const__folding_fold__nat__mod___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_const__folding_fold__bin__nat(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_const__folding_fold__nat__mod(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__mod___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_const__folding_fold__nat__mod___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_const__folding_fold__nat__mod(x_1);
return x_2;
}
}
obj* _init_l_lean_const__folding_bin__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; 
x_0 = lean::box(0);
x_1 = lean::mk_string("nat");
lean::inc(x_0);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("add");
lean::inc(x_3);
x_6 = lean_name_mk_string(x_3, x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__add___boxed), 1, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::mk_string("mul");
lean::inc(x_3);
x_11 = lean_name_mk_string(x_3, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__mul___boxed), 1, 0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::mk_string("div");
lean::inc(x_3);
x_16 = lean_name_mk_string(x_3, x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__div___boxed), 1, 0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::mk_string("mod");
x_20 = lean_name_mk_string(x_3, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_const__folding_fold__nat__mod___boxed), 1, 0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_18);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_8);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_const__folding_uint__bin__fold__fns;
lean::inc(x_27);
x_29 = l_list_append___rarg(x_27, x_26);
return x_29;
}
}
obj* l_lean_const__folding_find__bin__fold__fn__aux___main(obj* x_0, obj* x_1) {
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
obj* x_5; obj* x_7; obj* x_10; obj* x_12; uint8 x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean_name_dec_eq(x_0, x_10);
lean::dec(x_10);
if (x_15 == 0)
{
lean::dec(x_12);
x_1 = x_7;
goto _start;
}
else
{
obj* x_21; 
lean::dec(x_7);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_12);
return x_21;
}
}
}
}
obj* l_lean_const__folding_find__bin__fold__fn__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_const__folding_find__bin__fold__fn__aux___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_const__folding_find__bin__fold__fn(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_const__folding_bin__fold__fns;
lean::inc(x_1);
x_3 = l_lean_const__folding_find__bin__fold__fn__aux___main(x_0, x_1);
return x_3;
}
}
namespace lean {
obj* fold_bin_op_core(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::box(0);
return x_7;
}
case 1:
{
obj* x_11; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::box(0);
return x_11;
}
case 2:
{
obj* x_15; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_15 = lean::box(0);
return x_15;
}
case 3:
{
obj* x_19; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_19 = lean::box(0);
return x_19;
}
case 4:
{
obj* x_20; obj* x_23; obj* x_25; 
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
lean::dec(x_1);
x_23 = l_lean_const__folding_bin__fold__fns;
lean::inc(x_23);
x_25 = l_lean_const__folding_find__bin__fold__fn__aux___main(x_20, x_23);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; 
lean::dec(x_25);
lean::dec(x_3);
lean::dec(x_2);
x_29 = lean::box(0);
return x_29;
}
else
{
obj* x_30; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_25, 0);
lean::inc(x_30);
lean::dec(x_25);
x_33 = lean::box(x_0);
x_34 = lean::apply_3(x_30, x_33, x_2, x_3);
return x_34;
}
}
case 5:
{
obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_38 = lean::box(0);
return x_38;
}
case 6:
{
obj* x_42; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_42 = lean::box(0);
return x_42;
}
case 7:
{
obj* x_46; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_46 = lean::box(0);
return x_46;
}
case 8:
{
obj* x_50; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_50 = lean::box(0);
return x_50;
}
case 9:
{
obj* x_54; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_54 = lean::box(0);
return x_54;
}
case 10:
{
obj* x_58; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_58 = lean::box(0);
return x_58;
}
default:
{
obj* x_62; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_62 = lean::box(0);
return x_62;
}
}
}
}
}
obj* l_lean_const__folding_fold__bin__op___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = lean::fold_bin_op_core(x_4, x_1, x_2, x_3);
return x_5;
}
}
void initialize_init_lean_expr();
void initialize_init_platform();
void initialize_init_data_rbmap_default();
static bool _G_initialized = false;
void initialize_init_lean_compiler_const__folding() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_expr();
 initialize_init_platform();
 initialize_init_data_rbmap_default();
 l_lean_const__folding_bin__fold__fn = _init_l_lean_const__folding_bin__fold__fn();
 l_lean_const__folding_mk__uint__type__name___closed__1 = _init_l_lean_const__folding_mk__uint__type__name___closed__1();
 l_lean_const__folding_num__scalar__types = _init_l_lean_const__folding_num__scalar__types();
 l_lean_const__folding_fold__uint__add___closed__1 = _init_l_lean_const__folding_fold__uint__add___closed__1();
 l_lean_const__folding_fold__uint__mul___closed__1 = _init_l_lean_const__folding_fold__uint__mul___closed__1();
 l_lean_const__folding_fold__uint__div___closed__1 = _init_l_lean_const__folding_fold__uint__div___closed__1();
 l_lean_const__folding_fold__uint__mod___closed__1 = _init_l_lean_const__folding_fold__uint__mod___closed__1();
 l_lean_const__folding_fold__uint__sub___closed__1 = _init_l_lean_const__folding_fold__uint__sub___closed__1();
 l_lean_const__folding_pre__uint__bin__fold__fns = _init_l_lean_const__folding_pre__uint__bin__fold__fns();
 l_lean_const__folding_uint__bin__fold__fns = _init_l_lean_const__folding_uint__bin__fold__fns();
 l_lean_const__folding_fold__nat__add___rarg___closed__1 = _init_l_lean_const__folding_fold__nat__add___rarg___closed__1();
 l_lean_const__folding_fold__nat__mul___rarg___closed__1 = _init_l_lean_const__folding_fold__nat__mul___rarg___closed__1();
 l_lean_const__folding_fold__nat__div___rarg___closed__1 = _init_l_lean_const__folding_fold__nat__div___rarg___closed__1();
 l_lean_const__folding_fold__nat__mod___rarg___closed__1 = _init_l_lean_const__folding_fold__nat__mod___rarg___closed__1();
 l_lean_const__folding_bin__fold__fns = _init_l_lean_const__folding_bin__fold__fns();
}

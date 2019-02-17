// Lean compiler output
// Module: init.lean.compiler.const_folding
// Imports: init.lean.expr init.platform init.lean.compiler.util
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
obj* l_lean_compiler_get__info__from__fn(obj*, obj*);
obj* l_lean_compiler_fold__uint__mul___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_compiler_mk__nat__lt(obj*, obj*);
obj* l_lean_compiler_bin__fold__fns;
obj* l_nat_mod___boxed(obj*, obj*);
obj* l_lean_compiler_fold__nat__add(uint8);
extern obj* l_lean_mk__dec__is__true___closed__1;
obj* l_lean_compiler_fold__nat__dec__lt___closed__2;
obj* l_lean_compiler_is__of__nat(obj*);
obj* l___private_init_lean_compiler_const__folding_1__alist__find___main(obj*);
obj* l_lean_compiler_fold__char__of__nat___closed__1;
obj* l_lean_compiler_num__scalar__types;
obj* l_lean_compiler_mk__nat__eq___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_compiler_mk__nat__le(obj*, obj*);
obj* l_lean_compiler_fold__nat__div___rarg(obj*, obj*);
obj* l___private_init_lean_compiler_const__folding_1__alist__find___rarg(obj*, obj*);
obj* l_nat_mul___boxed(obj*, obj*);
extern obj* l_lean_compiler_mk__lc__proof___closed__1;
obj* l_lean_compiler_fold__uint__div___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_to__decidable__expr___closed__2;
namespace lean {
obj* nat_mod(obj*, obj*);
}
obj* l_lean_compiler_fold__uint__add___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_compiler_mk__nat__le___closed__1;
obj* l_lean_compiler_find__un__fold__fn(obj*);
namespace lean {
obj* fold_bin_op_core(uint8, obj*, obj*, obj*);
}
obj* l_lean_compiler_fold__uint__add___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_compiler_mk__uint__type__name___closed__1;
obj* l_lean_compiler_fold__nat__dec__eq___lambda__1___boxed(obj*, obj*);
extern obj* l_system_platform_nbits;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_compiler_fold__uint__mod(uint8, obj*, obj*);
obj* l_lean_compiler_fold__char__of__nat___boxed(obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_nat_add___boxed(obj*, obj*);
obj* l_list_foldr___main___at_lean_compiler_is__of__nat___spec__1(obj*, obj*);
obj* l_lean_compiler_fold__nat__succ___boxed(obj*);
obj* l_lean_compiler_fold__uint__div___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_compiler_get__info__from__fn___main(obj*, obj*);
obj* l_lean_compiler_uint__bin__fold__fns;
obj* l_lean_compiler_fold__nat__dec__eq(uint8, obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__le___closed__2;
obj* l_lean_compiler_fold__uint__sub(uint8, obj*, obj*);
obj* l_lean_compiler_fold__nat__add___boxed(obj*);
obj* l_lean_compiler_fold__uint__mod___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__eq___closed__2;
obj* l_lean_compiler_fold__nat__dec__le___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_lean_compiler_to__decidable__expr___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_to__decidable__expr(uint8, obj*, uint8);
obj* l_lean_compiler_fold__uint__div(uint8, obj*, obj*);
uint8 l_lean_compiler_fold__nat__dec__eq___lambda__1(obj*, obj*);
obj* l_lean_compiler_fold__nat__div___rarg___closed__1;
obj* l_lean_compiler_get__info__from__val(obj*);
obj* l_lean_compiler_fold__nat__mul___rarg___closed__1;
namespace lean {
obj* get_num_lit_core(obj*);
}
obj* l_lean_compiler_fold__nat__dec__le(uint8, obj*, obj*);
obj* l_lean_compiler_mk__uint32__lit___closed__1;
obj* l_lean_compiler_fold__uint__mod___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_compiler_nat__fold__fns;
obj* l_lean_compiler_fold__nat__dec__le___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__eq___closed__1;
obj* l_list_map___main___at_lean_compiler_uint__bin__fold__fns___spec__1(obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__lt___lambda__1___boxed(obj*, obj*);
obj* l_lean_compiler_fold__nat__add___rarg___closed__1;
obj* l_lean_compiler_fold__nat__mod___rarg(obj*, obj*);
obj* l_lean_compiler_fold__bin__uint___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_compiler_fold__nat__bin__pred(obj*, obj*, uint8, obj*, obj*);
obj* l_lean_compiler_fold__nat__mod___boxed(obj*);
obj* l_lean_compiler_fold__nat__succ(uint8);
obj* l_lean_compiler_fold__nat__bin__op(obj*, obj*, obj*);
obj* l_lean_compiler_fold__uint__sub___closed__1;
obj* l_lean_compiler_fold__nat__dec__lt___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_fold__char__of__nat(uint8, obj*);
obj* l_lean_compiler_fold__uint__add___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_fold__uint__sub___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__lt___closed__1;
obj* l_lean_name_append___main(obj*, obj*);
obj* l_lean_compiler_fold__nat__mod(uint8);
obj* l_lean_compiler_fold__un__op___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
uint8 l_lean_compiler_fold__nat__dec__le___lambda__1(obj*, obj*);
obj* l_lean_compiler_fold__uint__mul___closed__1;
obj* l_lean_compiler_fold__nat__mod___rarg___closed__1;
obj* l_lean_compiler_fold__nat__succ___rarg(obj*);
obj* l_lean_compiler_mk__nat__eq(obj*, obj*);
obj* l_lean_compiler_mk__uint__lit(obj*, obj*);
obj* l_lean_compiler_fold__bin__uint(obj*, uint8, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_lean_compiler_fold__uint__mul___lambda__1(obj*, uint8, obj*, obj*);
obj* l_lean_compiler_fold__nat__div(uint8);
obj* l_lean_mk__bin__app(obj*, obj*, obj*);
obj* l_lean_compiler_fold__nat__mul(uint8);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_compiler_mk__uint32__lit(obj*);
obj* l_nat_pow___main(obj*, obj*);
obj* l_lean_compiler_fold__uint__mul(uint8, obj*, obj*);
uint8 l_lean_compiler_fold__nat__dec__lt___lambda__1(obj*, obj*);
obj* l_lean_compiler_get__num__lit___main(obj*);
obj* l_lean_compiler_get__info__from__val___main(obj*);
obj* l_lean_compiler_fold__nat__bin__pred___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_compiler_fold__nat__mul___boxed(obj*);
obj* l_lean_compiler_to__decidable__expr___closed__1;
extern obj* l_lean_compiler_neutral__expr;
obj* l_lean_compiler_find__bin__fold__fn(obj*);
obj* l_lean_compiler_fold__nat__add___rarg(obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_lean_compiler_fold__uint__mod___closed__1;
extern obj* l_lean_level_one;
obj* l_lean_compiler_fold__nat__div___boxed(obj*);
obj* l_nat_repr(obj*);
obj* l_lean_compiler_bin__fold__fn;
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_lean_compiler_un__fold__fns;
obj* l_lean_compiler_fold__nat__dec__eq___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__le___lambda__1___boxed(obj*, obj*);
obj* l_lean_compiler_fold__nat__dec__lt(uint8, obj*, obj*);
obj* l_list_foldl___main___at_lean_compiler_uint__bin__fold__fns___spec__2(obj*, obj*);
obj* l_lean_compiler_fold__uint__sub___lambda__1___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_lean_compiler_const__folding_1__alist__find(obj*);
obj* l_lean_compiler_un__fold__fn;
obj* l_lean_compiler_fold__uint__div___closed__1;
obj* l_lean_compiler_fold__nat__mul___rarg(obj*, obj*);
obj* l_lean_compiler_fold__uint__mul___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_mk__uint__type__name(obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_compiler_fold__uint__mod___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_fold__uint__sub___boxed(obj*, obj*, obj*);
obj* l_lean_compiler_fold__bin__op___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_compiler_pre__uint__bin__fold__fns;
obj* l_lean_compiler_mk__nat__lt___closed__1;
obj* l_lean_compiler_fold__uint__div___lambda__1(obj*, uint8, obj*, obj*);
obj* l_nat_div___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
extern obj* l_lean_mk__dec__is__false___closed__1;
obj* l_lean_compiler_fold__uint__add___closed__1;
obj* l_lean_compiler_fold__uint__add(uint8, obj*, obj*);
namespace lean {
obj* fold_un_op_core(uint8, obj*, obj*);
}
obj* _init_l_lean_compiler_bin__fold__fn() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_compiler_un__fold__fn() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_compiler_mk__uint__type__name___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uint");
return x_0;
}
}
obj* l_lean_compiler_mk__uint__type__name(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_1 = l_nat_repr(x_0);
x_2 = l_lean_compiler_mk__uint__type__name___closed__1;
lean::inc(x_2);
x_4 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean_name_mk_string(x_6, x_4);
return x_7;
}
}
obj* _init_l_lean_compiler_num__scalar__types() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_0 = lean::mk_nat_obj(8u);
lean::inc(x_0);
x_2 = l_lean_compiler_mk__uint__type__name(x_0);
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
x_14 = l_lean_compiler_mk__uint__type__name(x_12);
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
x_24 = l_lean_compiler_mk__uint__type__name(x_22);
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
x_34 = l_lean_compiler_mk__uint__type__name(x_32);
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
x_44 = lean_name_mk_string(x_42, x_43);
lean::inc(x_44);
x_46 = lean_name_mk_string(x_44, x_3);
x_47 = l_system_platform_nbits;
lean::inc(x_47);
x_49 = l_nat_pow___main(x_7, x_47);
lean::inc(x_47);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_47);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_46);
lean::cnstr_set(x_51, 3, x_49);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_42);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_41);
lean::cnstr_set(x_53, 1, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_31);
lean::cnstr_set(x_54, 1, x_53);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_21);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_11);
lean::cnstr_set(x_56, 1, x_55);
return x_56;
}
}
obj* l_list_foldr___main___at_lean_compiler_is__of__nat___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 2);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean_name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_13 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
uint8 x_18; obj* x_19; 
lean::dec(x_7);
lean::dec(x_0);
x_18 = 1;
x_19 = lean::box(x_18);
return x_19;
}
}
}
}
obj* l_lean_compiler_is__of__nat(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_compiler_num__scalar__types;
lean::inc(x_1);
x_3 = l_list_foldr___main___at_lean_compiler_is__of__nat___spec__1(x_0, x_1);
return x_3;
}
}
obj* l_lean_compiler_get__info__from__fn___main(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_9; uint8 x_11; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
x_11 = lean_name_dec_eq(x_9, x_0);
lean::dec(x_9);
if (x_11 == 0)
{
lean::dec(x_4);
x_1 = x_6;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_6);
lean::dec(x_0);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_4);
return x_17;
}
}
}
}
obj* l_lean_compiler_get__info__from__fn(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_compiler_get__info__from__fn___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_compiler_get__info__from__val___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 5:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_4; obj* x_7; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_compiler_num__scalar__types;
lean::inc(x_7);
x_9 = l_lean_compiler_get__info__from__fn___main(x_4, x_7);
return x_9;
}
default:
{
obj* x_11; 
lean::dec(x_1);
x_11 = lean::box(0);
return x_11;
}
}
}
default:
{
obj* x_13; 
lean::dec(x_0);
x_13 = lean::box(0);
return x_13;
}
}
}
}
obj* l_lean_compiler_get__info__from__val(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_compiler_get__info__from__val___main(x_0);
return x_1;
}
}
obj* l_lean_compiler_get__num__lit___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 5:
{
obj* x_1; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_6; obj* x_9; obj* x_11; uint8 x_12; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_lean_compiler_num__scalar__types;
lean::inc(x_9);
x_11 = l_list_foldr___main___at_lean_compiler_is__of__nat___spec__1(x_6, x_9);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_3);
x_15 = lean::box(0);
return x_15;
}
else
{
x_0 = x_3;
goto _start;
}
}
default:
{
obj* x_19; 
lean::dec(x_1);
lean::dec(x_3);
x_19 = lean::box(0);
return x_19;
}
}
}
case 9:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_26; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_20);
x_28 = lean::box(0);
return x_28;
}
}
default:
{
obj* x_30; 
lean::dec(x_0);
x_30 = lean::box(0);
return x_30;
}
}
}
}
namespace lean {
obj* get_num_lit_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_compiler_get__num__lit___main(x_0);
return x_1;
}
}
}
obj* l_lean_compiler_mk__uint__lit(obj* x_0, obj* x_1) {
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
obj* _init_l_lean_compiler_mk__uint32__lit___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_0 = lean::mk_nat_obj(32u);
lean::inc(x_0);
x_2 = l_lean_compiler_mk__uint__type__name(x_0);
x_3 = lean::mk_string("of_nat");
lean::inc(x_2);
x_5 = lean_name_mk_string(x_2, x_3);
x_6 = lean::mk_nat_obj(2u);
lean::inc(x_0);
x_8 = l_nat_pow___main(x_6, x_0);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_5);
lean::cnstr_set(x_9, 3, x_8);
return x_9;
}
}
obj* l_lean_compiler_mk__uint32__lit(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_compiler_mk__uint32__lit___closed__1;
lean::inc(x_1);
x_3 = l_lean_compiler_mk__uint__lit(x_1, x_0);
return x_3;
}
}
obj* l_lean_compiler_fold__bin__uint(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::inc(x_2);
x_5 = l_lean_compiler_get__num__lit___main(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
}
x_13 = l_lean_compiler_get__num__lit___main(x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_18 = lean::box(0);
return x_18;
}
else
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_22 = l_lean_compiler_get__info__from__val___main(x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; 
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_19);
x_27 = lean::box(0);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
lean::dec(x_22);
x_31 = lean::box(x_1);
lean::inc(x_28);
x_33 = lean::apply_4(x_0, x_28, x_31, x_10, x_19);
x_34 = l_lean_compiler_mk__uint__lit(x_28, x_33);
if (lean::is_scalar(x_12)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_12;
}
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
obj* l_lean_compiler_fold__bin__uint___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_compiler_fold__bin__uint(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__add___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
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
obj* _init_l_lean_compiler_fold__uint__add___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__add___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__uint__add(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_compiler_fold__uint__add___closed__1;
lean::inc(x_3);
x_5 = l_lean_compiler_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__add___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_compiler_fold__uint__add___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__add___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__uint__add(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_compiler_fold__uint__mul___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
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
obj* _init_l_lean_compiler_fold__uint__mul___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__mul___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__uint__mul(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_compiler_fold__uint__mul___closed__1;
lean::inc(x_3);
x_5 = l_lean_compiler_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__mul___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_compiler_fold__uint__mul___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__mul___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__uint__mul(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_compiler_fold__uint__div___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
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
obj* _init_l_lean_compiler_fold__uint__div___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__div___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__uint__div(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_compiler_fold__uint__div___closed__1;
lean::inc(x_3);
x_5 = l_lean_compiler_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__div___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_compiler_fold__uint__div___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__div___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__uint__div(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_compiler_fold__uint__mod___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
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
obj* _init_l_lean_compiler_fold__uint__mod___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__mod___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__uint__mod(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_compiler_fold__uint__mod___closed__1;
lean::inc(x_3);
x_5 = l_lean_compiler_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__mod___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_compiler_fold__uint__mod___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__mod___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__uint__mod(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_compiler_fold__uint__sub___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
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
obj* _init_l_lean_compiler_fold__uint__sub___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__sub___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__uint__sub(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_compiler_fold__uint__sub___closed__1;
lean::inc(x_3);
x_5 = l_lean_compiler_fold__bin__uint(x_3, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__sub___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_compiler_fold__uint__sub___lambda__1(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_compiler_fold__uint__sub___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__uint__sub(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_lean_compiler_pre__uint__bin__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_0 = lean::box(0);
x_1 = lean::mk_string("add");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__add___boxed), 3, 0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("mul");
x_6 = lean_name_mk_string(x_0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__mul___boxed), 3, 0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::mk_string("div");
x_10 = lean_name_mk_string(x_0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__div___boxed), 3, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::mk_string("mod");
x_14 = lean_name_mk_string(x_0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__mod___boxed), 3, 0);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::mk_string("sub");
x_18 = lean_name_mk_string(x_0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__uint__sub___boxed), 3, 0);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_8);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
obj* l_list_map___main___at_lean_compiler_uint__bin__fold__fns___spec__1(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 x_8 = x_1;
}
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_13 = x_4;
}
lean::inc(x_0);
x_15 = l_list_map___main___at_lean_compiler_uint__bin__fold__fns___spec__1(x_0, x_6);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_lean_name_append___main(x_16, x_9);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_11);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_15);
return x_21;
}
}
}
obj* l_list_foldl___main___at_lean_compiler_uint__bin__fold__fns___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_compiler_pre__uint__bin__fold__fns;
lean::inc(x_7);
x_9 = l_list_map___main___at_lean_compiler_uint__bin__fold__fns___spec__1(x_2, x_7);
x_10 = l_list_append___rarg(x_0, x_9);
x_0 = x_10;
x_1 = x_4;
goto _start;
}
}
}
obj* _init_l_lean_compiler_uint__bin__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_compiler_num__scalar__types;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_lean_compiler_uint__bin__fold__fns___spec__2(x_0, x_1);
return x_3;
}
}
obj* l_lean_compiler_fold__nat__bin__op(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_compiler_get__num__lit___main(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_9 = x_3;
}
x_10 = l_lean_compiler_get__num__lit___main(x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_0);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::apply_2(x_0, x_7, x_15);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean_expr_mk_lit(x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
}
obj* _init_l_lean_compiler_fold__nat__add___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_add___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__add___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_fold__nat__add___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_compiler_fold__nat__bin__op(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_compiler_fold__nat__add(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__add___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_compiler_fold__nat__add___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_compiler_fold__nat__add(x_1);
return x_2;
}
}
obj* _init_l_lean_compiler_fold__nat__mul___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__mul___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_fold__nat__mul___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_compiler_fold__nat__bin__op(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_compiler_fold__nat__mul(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__mul___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_compiler_fold__nat__mul___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_compiler_fold__nat__mul(x_1);
return x_2;
}
}
obj* _init_l_lean_compiler_fold__nat__div___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_div___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__div___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_fold__nat__div___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_compiler_fold__nat__bin__op(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_compiler_fold__nat__div(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__div___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_compiler_fold__nat__div___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_compiler_fold__nat__div(x_1);
return x_2;
}
}
obj* _init_l_lean_compiler_fold__nat__mod___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_mod___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__mod___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_fold__nat__mod___rarg___closed__1;
lean::inc(x_2);
x_4 = l_lean_compiler_fold__nat__bin__op(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_compiler_fold__nat__mod(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__mod___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_compiler_fold__nat__mod___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_compiler_fold__nat__mod(x_1);
return x_2;
}
}
obj* _init_l_lean_compiler_mk__nat__eq___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::mk_string("eq");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_lean_level_one;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
x_6 = lean_expr_mk_const(x_2, x_5);
x_7 = lean::mk_string("nat");
x_8 = lean_name_mk_string(x_0, x_7);
x_9 = lean_expr_mk_const(x_8, x_0);
x_10 = lean_expr_mk_app(x_6, x_9);
return x_10;
}
}
obj* l_lean_compiler_mk__nat__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_mk__nat__eq___closed__1;
lean::inc(x_2);
x_4 = l_lean_mk__bin__app(x_2, x_0, x_1);
return x_4;
}
}
obj* _init_l_lean_compiler_mk__nat__lt___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("has_lt");
lean::inc(x_1);
x_3 = lean_name_mk_string(x_0, x_1);
x_4 = lean::mk_string("lt");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_0);
x_7 = lean_expr_mk_const(x_5, x_6);
x_8 = lean::mk_string("nat");
x_9 = lean_name_mk_string(x_0, x_8);
lean::inc(x_9);
x_11 = lean_expr_mk_const(x_9, x_0);
x_12 = lean_name_mk_string(x_9, x_1);
x_13 = lean_expr_mk_const(x_12, x_0);
x_14 = l_lean_mk__bin__app(x_7, x_11, x_13);
return x_14;
}
}
obj* l_lean_compiler_mk__nat__lt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_mk__nat__lt___closed__1;
lean::inc(x_2);
x_4 = l_lean_mk__bin__app(x_2, x_0, x_1);
return x_4;
}
}
obj* _init_l_lean_compiler_mk__nat__le___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("has_lt");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("le");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_0);
x_6 = lean_expr_mk_const(x_4, x_5);
x_7 = lean::mk_string("nat");
x_8 = lean_name_mk_string(x_0, x_7);
lean::inc(x_8);
x_10 = lean_expr_mk_const(x_8, x_0);
x_11 = lean::mk_string("has_le");
x_12 = lean_name_mk_string(x_8, x_11);
x_13 = lean_expr_mk_const(x_12, x_0);
x_14 = l_lean_mk__bin__app(x_6, x_10, x_13);
return x_14;
}
}
obj* l_lean_compiler_mk__nat__le(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_compiler_mk__nat__le___closed__1;
lean::inc(x_2);
x_4 = l_lean_mk__bin__app(x_2, x_0, x_1);
return x_4;
}
}
obj* _init_l_lean_compiler_to__decidable__expr___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_5; 
x_0 = l_lean_mk__dec__is__false___closed__1;
x_1 = l_lean_compiler_neutral__expr;
lean::inc(x_1);
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_mk__bin__app(x_0, x_1, x_1);
return x_5;
}
}
obj* _init_l_lean_compiler_to__decidable__expr___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_5; 
x_0 = l_lean_mk__dec__is__true___closed__1;
x_1 = l_lean_compiler_neutral__expr;
lean::inc(x_1);
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_mk__bin__app(x_0, x_1, x_1);
return x_5;
}
}
obj* l_lean_compiler_to__decidable__expr(uint8 x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_0 == 0)
{
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; 
x_4 = l_lean_compiler_to__decidable__expr___closed__1;
lean::inc(x_4);
return x_4;
}
else
{
obj* x_6; 
x_6 = l_lean_compiler_to__decidable__expr___closed__2;
lean::inc(x_6);
return x_6;
}
}
else
{
if (x_2 == 0)
{
obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_8 = l_lean_compiler_mk__lc__proof___closed__1;
lean::inc(x_1);
lean::inc(x_8);
x_11 = lean_expr_mk_app(x_8, x_1);
x_12 = l_lean_mk__dec__is__false___closed__1;
lean::inc(x_12);
x_14 = l_lean_mk__bin__app(x_12, x_1, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; 
x_15 = l_lean_compiler_mk__lc__proof___closed__1;
lean::inc(x_1);
lean::inc(x_15);
x_18 = lean_expr_mk_app(x_15, x_1);
x_19 = l_lean_mk__dec__is__true___closed__1;
lean::inc(x_19);
x_21 = l_lean_mk__bin__app(x_19, x_1, x_18);
return x_21;
}
}
}
}
obj* l_lean_compiler_to__decidable__expr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_0);
x_4 = lean::unbox(x_2);
x_5 = l_lean_compiler_to__decidable__expr(x_3, x_1, x_4);
return x_5;
}
}
obj* l_lean_compiler_fold__nat__bin__pred(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::inc(x_3);
x_6 = l_lean_compiler_get__num__lit___main(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; 
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_14 = x_6;
}
lean::inc(x_4);
x_16 = l_lean_compiler_get__num__lit___main(x_4);
if (lean::obj_tag(x_16) == 0)
{
obj* x_23; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_24; obj* x_27; obj* x_28; uint8 x_29; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::apply_2(x_0, x_3, x_4);
x_28 = lean::apply_2(x_1, x_12, x_24);
x_29 = lean::unbox(x_28);
lean::dec(x_28);
x_31 = l_lean_compiler_to__decidable__expr(x_2, x_27, x_29);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
}
}
}
obj* l_lean_compiler_fold__nat__bin__pred___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = l_lean_compiler_fold__nat__bin__pred(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
uint8 l_lean_compiler_fold__nat__dec__eq___lambda__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (x_2 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* _init_l_lean_compiler_fold__nat__dec__eq___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_mk__nat__eq), 2, 0);
return x_0;
}
}
obj* _init_l_lean_compiler_fold__nat__dec__eq___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__dec__eq___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__dec__eq(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_compiler_fold__nat__dec__eq___closed__1;
x_4 = l_lean_compiler_fold__nat__dec__eq___closed__2;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_compiler_fold__nat__bin__pred(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l_lean_compiler_fold__nat__dec__eq___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_compiler_fold__nat__dec__eq___lambda__1(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_compiler_fold__nat__dec__eq___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__nat__dec__eq(x_3, x_1, x_2);
return x_4;
}
}
uint8 l_lean_compiler_fold__nat__dec__lt___lambda__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (x_2 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* _init_l_lean_compiler_fold__nat__dec__lt___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_mk__nat__lt), 2, 0);
return x_0;
}
}
obj* _init_l_lean_compiler_fold__nat__dec__lt___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__dec__lt___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__dec__lt(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_compiler_fold__nat__dec__lt___closed__1;
x_4 = l_lean_compiler_fold__nat__dec__lt___closed__2;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_compiler_fold__nat__bin__pred(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l_lean_compiler_fold__nat__dec__lt___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_compiler_fold__nat__dec__lt___lambda__1(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_compiler_fold__nat__dec__lt___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__nat__dec__lt(x_3, x_1, x_2);
return x_4;
}
}
uint8 l_lean_compiler_fold__nat__dec__le___lambda__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_le(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
if (x_2 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* _init_l_lean_compiler_fold__nat__dec__le___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_mk__nat__le), 2, 0);
return x_0;
}
}
obj* _init_l_lean_compiler_fold__nat__dec__le___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__dec__le___lambda__1___boxed), 2, 0);
return x_0;
}
}
obj* l_lean_compiler_fold__nat__dec__le(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_compiler_fold__nat__dec__le___closed__1;
x_4 = l_lean_compiler_fold__nat__dec__le___closed__2;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_compiler_fold__nat__bin__pred(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l_lean_compiler_fold__nat__dec__le___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_compiler_fold__nat__dec__le___lambda__1(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_compiler_fold__nat__dec__le___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_compiler_fold__nat__dec__le(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_lean_compiler_nat__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_0 = lean::box(0);
x_1 = lean::mk_string("nat");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("add");
lean::inc(x_2);
x_5 = lean_name_mk_string(x_2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__add___boxed), 1, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::mk_string("mul");
lean::inc(x_2);
x_10 = lean_name_mk_string(x_2, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__mul___boxed), 1, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::mk_string("div");
lean::inc(x_2);
x_15 = lean_name_mk_string(x_2, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__div___boxed), 1, 0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::mk_string("mod");
lean::inc(x_2);
x_20 = lean_name_mk_string(x_2, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__mod___boxed), 1, 0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::mk_string("dec_eq");
lean::inc(x_2);
x_25 = lean_name_mk_string(x_2, x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__dec__eq___boxed), 3, 0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_string("dec_lt");
lean::inc(x_2);
x_30 = lean_name_mk_string(x_2, x_28);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__dec__lt___boxed), 3, 0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::mk_string("dec_le");
x_34 = lean_name_mk_string(x_2, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__dec__le___boxed), 3, 0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_0);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_32);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_27);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_22);
lean::cnstr_set(x_40, 1, x_39);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_17);
lean::cnstr_set(x_41, 1, x_40);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_12);
lean::cnstr_set(x_42, 1, x_41);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_7);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
obj* _init_l_lean_compiler_bin__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_compiler_uint__bin__fold__fns;
x_1 = l_lean_compiler_nat__fold__fns;
lean::inc(x_1);
lean::inc(x_0);
x_4 = l_list_append___rarg(x_0, x_1);
return x_4;
}
}
obj* l_lean_compiler_fold__nat__succ___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_compiler_get__num__lit___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
}
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_3, x_6);
lean::dec(x_6);
lean::dec(x_3);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_11 = lean_expr_mk_lit(x_10);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_lean_compiler_fold__nat__succ(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__succ___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_compiler_fold__nat__succ___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_compiler_fold__nat__succ(x_1);
return x_2;
}
}
obj* _init_l_lean_compiler_fold__char__of__nat___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_compiler_mk__uint32__lit___closed__1;
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_3 = l_lean_compiler_mk__uint__lit(x_0, x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_lean_compiler_fold__char__of__nat(uint8 x_0, obj* x_1) {
_start:
{
obj* x_2; 
if (x_0 == 0)
{
obj* x_4; 
x_4 = lean::box(0);
x_2 = x_4;
goto lbl_3;
}
else
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::box(0);
return x_6;
}
lbl_3:
{
obj* x_8; 
lean::dec(x_2);
x_8 = l_lean_compiler_get__num__lit___main(x_1);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_12; uint32 x_13; uint32 x_14; uint8 x_15; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_12 = x_8;
}
x_13 = lean::uint32_of_nat(x_10);
x_14 = 55296;
x_15 = x_13 < x_14;
if (x_15 == 0)
{
uint32 x_16; uint8 x_17; 
x_16 = 57343;
x_17 = x_16 < x_13;
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_10);
lean::dec(x_12);
x_20 = l_lean_compiler_fold__char__of__nat___closed__1;
lean::inc(x_20);
return x_20;
}
else
{
uint32 x_22; uint8 x_23; 
x_22 = 1114112;
x_23 = x_13 < x_22;
if (x_23 == 0)
{
obj* x_26; 
lean::dec(x_10);
lean::dec(x_12);
x_26 = l_lean_compiler_fold__char__of__nat___closed__1;
lean::inc(x_26);
return x_26;
}
else
{
obj* x_28; obj* x_30; obj* x_31; 
x_28 = l_lean_compiler_mk__uint32__lit___closed__1;
lean::inc(x_28);
x_30 = l_lean_compiler_mk__uint__lit(x_28, x_10);
if (lean::is_scalar(x_12)) {
 x_31 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_31 = x_12;
}
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
obj* x_32; obj* x_34; obj* x_35; 
x_32 = l_lean_compiler_mk__uint32__lit___closed__1;
lean::inc(x_32);
x_34 = l_lean_compiler_mk__uint__lit(x_32, x_10);
if (lean::is_scalar(x_12)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_12;
}
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
obj* l_lean_compiler_fold__char__of__nat___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_lean_compiler_fold__char__of__nat(x_2, x_1);
return x_3;
}
}
obj* _init_l_lean_compiler_un__fold__fns() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::mk_string("nat");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("succ");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__nat__succ___boxed), 1, 0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("char");
x_8 = lean_name_mk_string(x_0, x_7);
x_9 = lean::mk_string("of_nat");
x_10 = lean_name_mk_string(x_8, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_compiler_fold__char__of__nat___boxed), 2, 0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
obj* l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; uint8 x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean_name_dec_eq(x_0, x_9);
lean::dec(x_9);
if (x_14 == 0)
{
lean::dec(x_11);
x_1 = x_6;
goto _start;
}
else
{
obj* x_20; 
lean::dec(x_6);
lean::dec(x_0);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_11);
return x_20;
}
}
}
}
obj* l___private_init_lean_compiler_const__folding_1__alist__find___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_compiler_const__folding_1__alist__find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_const__folding_1__alist__find(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_const__folding_1__alist__find___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_compiler_find__bin__fold__fn(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_compiler_bin__fold__fns;
lean::inc(x_1);
x_3 = l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(x_0, x_1);
return x_3;
}
}
obj* l_lean_compiler_find__un__fold__fn(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_compiler_un__fold__fns;
lean::inc(x_1);
x_3 = l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(x_0, x_1);
return x_3;
}
}
namespace lean {
obj* fold_bin_op_core(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_4; obj* x_7; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_lean_compiler_bin__fold__fns;
lean::inc(x_7);
x_9 = l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(x_4, x_7);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; 
lean::dec(x_3);
lean::dec(x_2);
x_12 = lean::box(0);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_16 = lean::box(x_0);
x_17 = lean::apply_3(x_13, x_16, x_2, x_3);
return x_17;
}
}
default:
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_21 = lean::box(0);
return x_21;
}
}
}
}
}
obj* l_lean_compiler_fold__bin__op___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = lean::fold_bin_op_core(x_4, x_1, x_2, x_3);
return x_5;
}
}
namespace lean {
obj* fold_un_op_core(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 4:
{
obj* x_3; obj* x_6; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = l_lean_compiler_un__fold__fns;
lean::inc(x_6);
x_8 = l___private_init_lean_compiler_const__folding_1__alist__find___main___rarg(x_3, x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_2);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::box(x_0);
x_15 = lean::apply_2(x_11, x_14, x_2);
return x_15;
}
}
default:
{
obj* x_18; 
lean::dec(x_1);
lean::dec(x_2);
x_18 = lean::box(0);
return x_18;
}
}
}
}
}
obj* l_lean_compiler_fold__un__op___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = lean::fold_un_op_core(x_3, x_1, x_2);
return x_4;
}
}
void initialize_init_lean_expr();
void initialize_init_platform();
void initialize_init_lean_compiler_util();
static bool _G_initialized = false;
void initialize_init_lean_compiler_const__folding() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_expr();
 initialize_init_platform();
 initialize_init_lean_compiler_util();
 l_lean_compiler_bin__fold__fn = _init_l_lean_compiler_bin__fold__fn();
 l_lean_compiler_un__fold__fn = _init_l_lean_compiler_un__fold__fn();
 l_lean_compiler_mk__uint__type__name___closed__1 = _init_l_lean_compiler_mk__uint__type__name___closed__1();
 l_lean_compiler_num__scalar__types = _init_l_lean_compiler_num__scalar__types();
 l_lean_compiler_mk__uint32__lit___closed__1 = _init_l_lean_compiler_mk__uint32__lit___closed__1();
 l_lean_compiler_fold__uint__add___closed__1 = _init_l_lean_compiler_fold__uint__add___closed__1();
 l_lean_compiler_fold__uint__mul___closed__1 = _init_l_lean_compiler_fold__uint__mul___closed__1();
 l_lean_compiler_fold__uint__div___closed__1 = _init_l_lean_compiler_fold__uint__div___closed__1();
 l_lean_compiler_fold__uint__mod___closed__1 = _init_l_lean_compiler_fold__uint__mod___closed__1();
 l_lean_compiler_fold__uint__sub___closed__1 = _init_l_lean_compiler_fold__uint__sub___closed__1();
 l_lean_compiler_pre__uint__bin__fold__fns = _init_l_lean_compiler_pre__uint__bin__fold__fns();
 l_lean_compiler_uint__bin__fold__fns = _init_l_lean_compiler_uint__bin__fold__fns();
 l_lean_compiler_fold__nat__add___rarg___closed__1 = _init_l_lean_compiler_fold__nat__add___rarg___closed__1();
 l_lean_compiler_fold__nat__mul___rarg___closed__1 = _init_l_lean_compiler_fold__nat__mul___rarg___closed__1();
 l_lean_compiler_fold__nat__div___rarg___closed__1 = _init_l_lean_compiler_fold__nat__div___rarg___closed__1();
 l_lean_compiler_fold__nat__mod___rarg___closed__1 = _init_l_lean_compiler_fold__nat__mod___rarg___closed__1();
 l_lean_compiler_mk__nat__eq___closed__1 = _init_l_lean_compiler_mk__nat__eq___closed__1();
 l_lean_compiler_mk__nat__lt___closed__1 = _init_l_lean_compiler_mk__nat__lt___closed__1();
 l_lean_compiler_mk__nat__le___closed__1 = _init_l_lean_compiler_mk__nat__le___closed__1();
 l_lean_compiler_to__decidable__expr___closed__1 = _init_l_lean_compiler_to__decidable__expr___closed__1();
 l_lean_compiler_to__decidable__expr___closed__2 = _init_l_lean_compiler_to__decidable__expr___closed__2();
 l_lean_compiler_fold__nat__dec__eq___closed__1 = _init_l_lean_compiler_fold__nat__dec__eq___closed__1();
 l_lean_compiler_fold__nat__dec__eq___closed__2 = _init_l_lean_compiler_fold__nat__dec__eq___closed__2();
 l_lean_compiler_fold__nat__dec__lt___closed__1 = _init_l_lean_compiler_fold__nat__dec__lt___closed__1();
 l_lean_compiler_fold__nat__dec__lt___closed__2 = _init_l_lean_compiler_fold__nat__dec__lt___closed__2();
 l_lean_compiler_fold__nat__dec__le___closed__1 = _init_l_lean_compiler_fold__nat__dec__le___closed__1();
 l_lean_compiler_fold__nat__dec__le___closed__2 = _init_l_lean_compiler_fold__nat__dec__le___closed__2();
 l_lean_compiler_nat__fold__fns = _init_l_lean_compiler_nat__fold__fns();
 l_lean_compiler_bin__fold__fns = _init_l_lean_compiler_bin__fold__fns();
 l_lean_compiler_fold__char__of__nat___closed__1 = _init_l_lean_compiler_fold__char__of__nat___closed__1();
 l_lean_compiler_un__fold__fns = _init_l_lean_compiler_un__fold__fns();
}

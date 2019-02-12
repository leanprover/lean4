// Lean compiler output
// Module: init.lean.position
// Imports: init.data.nat.default init.data.rbmap.default init.lean.format
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
uint8 l_prod__has__decidable__lt___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_position_lean_has__to__format___closed__1;
obj* l_rbmap_of__list___main___at_lean_file__map_from__string___spec__1(obj*);
obj* l_lean_position_lt;
obj* l_lean_position_lean_has__to__format(obj*);
obj* l___private_3205843539__from__string__aux(obj*, obj*, obj*);
obj* l_lean_position_has__lt;
obj* l_lean_position_decidable__lt___boxed(obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_lean_position_lean_has__to__format___closed__2;
uint8 l_lean_position_decidable__lt(obj*, obj*);
obj* l_lean_position_decidable__lt___main___boxed(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_file__map_from__string___spec__2(obj*, obj*, obj*);
obj* l_lean_position_decidable__lt___main___closed__2;
obj* l_nat_dec__eq___boxed(obj*, obj*);
obj* l_lean_file__map_from__string(obj*);
obj* l___private_3205843539__from__string__aux___main(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_position_lean_has__to__format___spec__1(obj*);
obj* l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(obj*, obj*, obj*);
obj* l_lean_position_lean_has__to__format___closed__3;
obj* l_rbnode_lower__bound___main___at_lean_file__map_to__position___spec__2(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_file__map_from__string___spec__3(obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_position_decidable__lt___main___closed__1;
obj* l_rbmap_lower__bound___main___at_lean_file__map_to__position___spec__1(obj*, obj*);
obj* l_nat_repr(obj*);
uint8 l_lean_position_decidable__lt___main(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_lean_position_lt___main;
obj* l_lean_position_inhabited;
uint8 l_lean_position_decidable__eq(obj*, obj*);
obj* l_nat_dec__lt___boxed(obj*, obj*);
obj* l_lean_position_decidable__eq___boxed(obj*, obj*);
uint8 l_lean_position_decidable__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; uint8 x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::nat_dec_eq(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
if (x_12 == 0)
{
uint8 x_17; 
lean::dec(x_9);
lean::dec(x_4);
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = lean::nat_dec_eq(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
if (x_18 == 0)
{
uint8 x_21; 
x_21 = 0;
return x_21;
}
else
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
}
}
}
obj* l_lean_position_decidable__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_position_decidable__eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_lean_position_lt___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_position_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_position_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_position_decidable__lt___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_lean_position_decidable__lt___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_dec__lt___boxed), 2, 0);
return x_0;
}
}
uint8 l_lean_position_decidable__lt___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_20; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_4);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_9);
x_14 = l_lean_position_decidable__lt___main___closed__1;
x_15 = l_lean_position_decidable__lt___main___closed__2;
lean::inc(x_15);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_14);
x_20 = l_prod__has__decidable__lt___rarg(x_14, x_14, x_15, x_15, x_12, x_13);
return x_20;
}
}
obj* l_lean_position_decidable__lt___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_position_decidable__lt___main(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_lean_position_decidable__lt(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_position_decidable__lt___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_position_decidable__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_position_decidable__lt(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_to__fmt___at_lean_position_lean_has__to__format___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_nat_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_position_lean_has__to__format___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x9f\xa8");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_position_lean_has__to__format___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(", ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_position_lean_has__to__format___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x9f\xa9");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_position_lean_has__to__format(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; uint8 x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_to__fmt___at_lean_position_lean_has__to__format___spec__1(x_1);
x_7 = 0;
x_8 = l_lean_position_lean_has__to__format___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
x_11 = x_10;
x_12 = l_lean_position_lean_has__to__format___closed__2;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_7);
x_15 = x_14;
x_16 = l_lean_to__fmt___at_lean_position_lean_has__to__format___spec__1(x_3);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_7);
x_18 = x_17;
x_19 = l_lean_position_lean_has__to__format___closed__3;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_7);
x_22 = x_21;
return x_22;
}
}
obj* _init_l_lean_position_inhabited() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l___private_3205843539__from__string__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_8; uint8 x_10; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_0);
x_10 = lean::string_iterator_has_next(x_1);
if (x_10 == 0)
{
obj* x_16; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::box(0);
x_8 = x_17;
goto lbl_9;
}
lbl_9:
{
uint32 x_19; obj* x_20; obj* x_21; uint8 x_22; uint32 x_24; 
lean::dec(x_8);
x_19 = lean::string_iterator_curr(x_1);
x_20 = lean::mk_nat_obj(10u);
x_21 = lean::mk_nat_obj(55296u);
x_22 = lean::nat_dec_lt(x_20, x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = lean::mk_nat_obj(57343u);
x_27 = lean::nat_dec_lt(x_26, x_20);
lean::dec(x_26);
if (x_27 == 0)
{
uint32 x_30; 
lean::dec(x_20);
x_30 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_24 = x_30;
goto lbl_25;
}
else
{
obj* x_32; uint8 x_33; 
x_32 = lean::mk_nat_obj(1114112u);
x_33 = lean::nat_dec_lt(x_20, x_32);
lean::dec(x_32);
if (x_33 == 0)
{
uint32 x_36; 
lean::dec(x_20);
x_36 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_24 = x_36;
goto lbl_25;
}
else
{
uint32 x_39; 
lean::dec(x_3);
x_39 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_24 = x_39;
goto lbl_25;
}
}
}
else
{
uint32 x_42; 
lean::dec(x_3);
x_42 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_24 = x_42;
goto lbl_25;
}
lbl_25:
{
obj* x_44; obj* x_45; uint8 x_46; 
x_44 = lean::box_uint32(x_19);
x_45 = lean::box_uint32(x_24);
x_46 = lean::nat_dec_eq(x_44, x_45);
lean::dec(x_45);
lean::dec(x_44);
if (x_46 == 0)
{
obj* x_50; 
lean::dec(x_5);
x_50 = lean::string_iterator_next(x_1);
x_0 = x_6;
x_1 = x_50;
goto _start;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_58; obj* x_59; obj* x_60; 
x_52 = lean::string_iterator_next(x_1);
x_53 = lean::string_iterator_offset(x_52);
x_54 = lean::nat_add(x_2, x_5);
lean::dec(x_5);
lean::dec(x_2);
lean::inc(x_54);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_54);
x_59 = l___private_3205843539__from__string__aux___main(x_6, x_52, x_54);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
obj* x_65; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_65 = lean::box(0);
return x_65;
}
}
}
obj* l___private_3205843539__from__string__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_3205843539__from__string__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
x_14 = lean::nat_dec_lt(x_1, x_7);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = lean::nat_dec_lt(x_7, x_1);
if (x_15 == 0)
{
obj* x_18; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_1);
lean::cnstr_set(x_18, 2, x_2);
lean::cnstr_set(x_18, 3, x_11);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_7);
lean::cnstr_set(x_20, 2, x_9);
lean::cnstr_set(x_20, 3, x_19);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_22 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_22 = x_13;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_7);
lean::cnstr_set(x_22, 2, x_9);
lean::cnstr_set(x_22, 3, x_11);
return x_22;
}
}
default:
{
obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; uint8 x_32; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_0, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 2);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 3);
lean::inc(x_29);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_31 = x_0;
}
x_32 = lean::nat_dec_lt(x_1, x_25);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = lean::nat_dec_lt(x_25, x_1);
if (x_33 == 0)
{
obj* x_36; 
lean::dec(x_25);
lean::dec(x_27);
if (lean::is_scalar(x_31)) {
 x_36 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_36 = x_31;
}
lean::cnstr_set(x_36, 0, x_23);
lean::cnstr_set(x_36, 1, x_1);
lean::cnstr_set(x_36, 2, x_2);
lean::cnstr_set(x_36, 3, x_29);
return x_36;
}
else
{
uint8 x_38; 
lean::inc(x_29);
x_38 = l_rbnode_get__color___main___rarg(x_29);
if (x_38 == 0)
{
obj* x_40; obj* x_41; 
lean::dec(x_31);
x_40 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_29, x_1, x_2);
x_41 = l_rbnode_balance2__node___main___rarg(x_40, x_25, x_27, x_23);
return x_41;
}
else
{
obj* x_42; obj* x_43; 
x_42 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_29, x_1, x_2);
if (lean::is_scalar(x_31)) {
 x_43 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_43 = x_31;
}
lean::cnstr_set(x_43, 0, x_23);
lean::cnstr_set(x_43, 1, x_25);
lean::cnstr_set(x_43, 2, x_27);
lean::cnstr_set(x_43, 3, x_42);
return x_43;
}
}
}
else
{
uint8 x_45; 
lean::inc(x_23);
x_45 = l_rbnode_get__color___main___rarg(x_23);
if (x_45 == 0)
{
obj* x_47; obj* x_48; 
lean::dec(x_31);
x_47 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_23, x_1, x_2);
x_48 = l_rbnode_balance1__node___main___rarg(x_47, x_25, x_27, x_29);
return x_48;
}
else
{
obj* x_49; obj* x_50; 
x_49 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_23, x_1, x_2);
if (lean::is_scalar(x_31)) {
 x_50 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_50 = x_31;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_25);
lean::cnstr_set(x_50, 2, x_27);
lean::cnstr_set(x_50, 3, x_29);
return x_50;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_file__map_from__string___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_file__map_from__string___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_file__map_from__string___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_of__list___main___at_lean_file__map_from__string___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_rbmap_of__list___main___at_lean_file__map_from__string___spec__1(x_5);
x_14 = l_rbnode_insert___at_lean_file__map_from__string___spec__3(x_13, x_8, x_10);
return x_14;
}
}
}
obj* l_lean_file__map_from__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::mk_nat_obj(1u);
x_4 = l___private_3205843539__from__string__aux___main(x_1, x_2, x_3);
x_5 = l_rbmap_of__list___main___at_lean_file__map_from__string___spec__1(x_4);
return x_5;
}
}
obj* l_rbnode_lower__bound___main___at_lean_file__map_to__position___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_14; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::nat_dec_lt(x_1, x_7);
if (x_14 == 0)
{
uint8 x_17; 
lean::dec(x_5);
lean::dec(x_2);
x_17 = lean::nat_dec_lt(x_7, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_1);
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_9);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_9);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_0 = x_11;
x_2 = x_23;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; uint8 x_38; 
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 2);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 3);
lean::inc(x_35);
lean::dec(x_0);
x_38 = lean::nat_dec_lt(x_1, x_31);
if (x_38 == 0)
{
uint8 x_41; 
lean::dec(x_29);
lean::dec(x_2);
x_41 = lean::nat_dec_lt(x_31, x_1);
if (x_41 == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_1);
lean::dec(x_35);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_31);
lean::cnstr_set(x_44, 1, x_33);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_31);
lean::cnstr_set(x_46, 1, x_33);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_0 = x_35;
x_2 = x_47;
goto _start;
}
}
else
{
lean::dec(x_31);
lean::dec(x_33);
lean::dec(x_35);
x_0 = x_29;
goto _start;
}
}
}
}
}
obj* l_rbmap_lower__bound___main___at_lean_file__map_to__position___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_rbnode_lower__bound___main___at_lean_file__map_to__position___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_file__map_to__position(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::inc(x_1);
x_3 = l_rbmap_lower__bound___main___at_lean_file__map_to__position___spec__1(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_18; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
}
void initialize_init_data_nat_default();
void initialize_init_data_rbmap_default();
void initialize_init_lean_format();
static bool _G_initialized = false;
void initialize_init_lean_position() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_default();
 initialize_init_data_rbmap_default();
 initialize_init_lean_format();
 l_lean_position_lt___main = _init_l_lean_position_lt___main();
 l_lean_position_lt = _init_l_lean_position_lt();
 l_lean_position_has__lt = _init_l_lean_position_has__lt();
 l_lean_position_decidable__lt___main___closed__1 = _init_l_lean_position_decidable__lt___main___closed__1();
 l_lean_position_decidable__lt___main___closed__2 = _init_l_lean_position_decidable__lt___main___closed__2();
 l_lean_position_lean_has__to__format___closed__1 = _init_l_lean_position_lean_has__to__format___closed__1();
 l_lean_position_lean_has__to__format___closed__2 = _init_l_lean_position_lean_has__to__format___closed__2();
 l_lean_position_lean_has__to__format___closed__3 = _init_l_lean_position_lean_has__to__format___closed__3();
 l_lean_position_inhabited = _init_l_lean_position_inhabited();
}

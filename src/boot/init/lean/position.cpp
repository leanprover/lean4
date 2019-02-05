// Lean compiler output
// Module: init.lean.position
// Imports: init.data.nat.default init.data.rbmap.default init.lean.format
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
unsigned char l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_position_decidable__lt___main___closed__1;
obj* l_lean_position_inhabited;
obj* l_prod__has__decidable__lt___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_167970869__from__string__aux___main(obj*, obj*, obj*);
obj* l_rbmap_lower__bound___main___at_lean_file__map_to__position___spec__1(obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_file__map_from__string___spec__2(obj*, obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_position_lean_has__to__format___closed__1;
obj* l_lean_position_has__lt;
obj* l_lean_position_decidable__lt___main(obj*, obj*);
obj* l_lean_position_lean_has__to__format(obj*);
obj* l_lean_position_decidable__eq(obj*, obj*);
obj* l_lean_position_decidable__lt___main___closed__2;
obj* l___private_167970869__from__string__aux(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_position_lean_has__to__format___spec__1(obj*);
obj* l_lean_position_lt___main;
obj* l_lean_position_lt;
obj* l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_file__map_from__string___spec__3(obj*, obj*, obj*);
obj* l_lean_position_lean_has__to__format___closed__3;
obj* l_lean_file__map_from__string(obj*);
obj* l_nat_repr(obj*);
obj* l_lean_position_lean_has__to__format___closed__2;
obj* l_rbnode_lower__bound___main___at_lean_file__map_to__position___spec__2(obj*, obj*, obj*);
obj* l_lean_position_decidable__lt(obj*, obj*);
obj* l_rbmap_of__list___main___at_lean_file__map_from__string___spec__1(obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(unsigned char, obj*);
obj* l_lean_position_decidable__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; 
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
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; 
lean::dec(x_9);
lean::dec(x_12);
lean::dec(x_4);
x_18 = lean::box(0);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_12);
x_20 = lean::nat_dec_eq(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
return x_20;
}
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
obj* l_lean_position_decidable__lt___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_20; 
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
obj* _init_l_lean_position_decidable__lt___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_dec_eq), 2, 0);
return x_0;
}
}
obj* _init_l_lean_position_decidable__lt___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_dec_lt), 2, 0);
return x_0;
}
}
obj* l_lean_position_decidable__lt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_position_decidable__lt___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_position_lean_has__to__format(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; unsigned char x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
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
obj* l___private_167970869__from__string__aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_9; unsigned char x_11; 
lean::dec(x_4);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_0, x_6);
lean::dec(x_0);
x_11 = lean::string_iterator_has_next(x_1);
if (x_11 == 0)
{
obj* x_17; 
lean::dec(x_6);
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; 
x_18 = lean::box(0);
x_9 = x_18;
goto lbl_10;
}
lbl_10:
{
unsigned x_20; obj* x_21; obj* x_22; obj* x_23; unsigned x_25; 
lean::dec(x_9);
x_20 = lean::string_iterator_curr(x_1);
x_21 = lean::mk_nat_obj(10u);
x_22 = lean::mk_nat_obj(55296u);
x_23 = lean::nat_dec_lt(x_21, x_22);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_23);
x_28 = lean::mk_nat_obj(57343u);
x_29 = lean::nat_dec_lt(x_28, x_21);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
unsigned x_33; 
lean::dec(x_21);
lean::dec(x_29);
x_33 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_25 = x_33;
goto lbl_26;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_29);
x_36 = lean::mk_nat_obj(1114112u);
x_37 = lean::nat_dec_lt(x_21, x_36);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
unsigned x_41; 
lean::dec(x_21);
lean::dec(x_37);
x_41 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_25 = x_41;
goto lbl_26;
}
else
{
unsigned x_45; 
lean::dec(x_3);
lean::dec(x_37);
x_45 = lean::unbox_uint32(x_21);
lean::dec(x_21);
x_25 = x_45;
goto lbl_26;
}
}
}
else
{
unsigned x_49; 
lean::dec(x_23);
lean::dec(x_3);
x_49 = lean::unbox_uint32(x_21);
lean::dec(x_21);
x_25 = x_49;
goto lbl_26;
}
lbl_26:
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = lean::box_uint32(x_20);
x_52 = lean::box_uint32(x_25);
x_53 = lean::nat_dec_eq(x_51, x_52);
lean::dec(x_52);
lean::dec(x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; 
lean::dec(x_53);
lean::dec(x_6);
x_58 = lean::string_iterator_next(x_1);
x_0 = x_7;
x_1 = x_58;
goto _start;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_53);
x_61 = lean::string_iterator_next(x_1);
x_62 = lean::string_iterator_offset(x_61);
x_63 = lean::nat_add(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
lean::inc(x_63);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_62);
lean::cnstr_set(x_67, 1, x_63);
x_68 = l___private_167970869__from__string__aux___main(x_7, x_61, x_63);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
obj* x_75; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_75 = lean::box(0);
return x_75;
}
}
}
obj* l___private_167970869__from__string__aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_167970869__from__string__aux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_file__map_from__string(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::mk_nat_obj(1u);
x_4 = l___private_167970869__from__string__aux___main(x_1, x_2, x_3);
x_5 = l_rbmap_of__list___main___at_lean_file__map_from__string___spec__1(x_4);
return x_5;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; 
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
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; 
lean::dec(x_14);
x_16 = lean::nat_dec_lt(x_7, x_1);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_9);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_11);
return x_20;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_16);
x_22 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_23 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_23 = x_13;
}
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_7);
lean::cnstr_set(x_23, 2, x_9);
lean::cnstr_set(x_23, 3, x_22);
return x_23;
}
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_14);
x_25 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_7);
lean::cnstr_set(x_26, 2, x_9);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
}
default:
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; 
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 2);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 3);
lean::inc(x_33);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_35 = x_0;
}
x_36 = lean::nat_dec_lt(x_1, x_29);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; 
lean::dec(x_36);
x_38 = lean::nat_dec_lt(x_29, x_1);
if (lean::obj_tag(x_38) == 0)
{
obj* x_42; 
lean::dec(x_38);
lean::dec(x_29);
lean::dec(x_31);
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_27);
lean::cnstr_set(x_42, 1, x_1);
lean::cnstr_set(x_42, 2, x_2);
lean::cnstr_set(x_42, 3, x_33);
return x_42;
}
else
{
unsigned char x_45; 
lean::dec(x_38);
lean::inc(x_33);
x_45 = l_rbnode_get__color___main___rarg(x_33);
if (x_45 == 0)
{
obj* x_47; obj* x_48; 
lean::dec(x_35);
x_47 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_33, x_1, x_2);
x_48 = l_rbnode_balance2__node___main___rarg(x_47, x_29, x_31, x_27);
return x_48;
}
else
{
obj* x_49; obj* x_50; 
x_49 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_33, x_1, x_2);
if (lean::is_scalar(x_35)) {
 x_50 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_50 = x_35;
}
lean::cnstr_set(x_50, 0, x_27);
lean::cnstr_set(x_50, 1, x_29);
lean::cnstr_set(x_50, 2, x_31);
lean::cnstr_set(x_50, 3, x_49);
return x_50;
}
}
}
else
{
unsigned char x_53; 
lean::dec(x_36);
lean::inc(x_27);
x_53 = l_rbnode_get__color___main___rarg(x_27);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_35);
x_55 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_27, x_1, x_2);
x_56 = l_rbnode_balance1__node___main___rarg(x_55, x_29, x_31, x_33);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_file__map_from__string___spec__4(x_27, x_1, x_2);
if (lean::is_scalar(x_35)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_35;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_29);
lean::cnstr_set(x_58, 2, x_31);
lean::cnstr_set(x_58, 3, x_33);
return x_58;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_file__map_from__string___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
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
obj* l_rbnode_lower__bound___main___at_lean_file__map_to__position___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; 
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
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; 
lean::dec(x_14);
lean::dec(x_2);
lean::dec(x_5);
x_18 = lean::nat_dec_lt(x_7, x_1);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_1);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_9);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_18);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_0 = x_11;
x_2 = x_26;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_14);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
lean::dec(x_0);
x_42 = lean::nat_dec_lt(x_1, x_35);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; 
lean::dec(x_42);
lean::dec(x_2);
lean::dec(x_33);
x_46 = lean::nat_dec_lt(x_35, x_1);
if (lean::obj_tag(x_46) == 0)
{
obj* x_50; obj* x_51; 
lean::dec(x_46);
lean::dec(x_1);
lean::dec(x_39);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_35);
lean::cnstr_set(x_50, 1, x_37);
x_51 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
else
{
obj* x_53; obj* x_54; 
lean::dec(x_46);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_35);
lean::cnstr_set(x_53, 1, x_37);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_0 = x_39;
x_2 = x_54;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_33;
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

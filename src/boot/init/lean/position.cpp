// Lean compiler output
// Module: init.lean.position
// Imports: init.data.nat.default init.data.rbmap.default init.lean.format
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
unsigned char _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__1;
obj* _l_s4_lean_s8_position_s9_inhabited;
obj* _l_s24_prod__has__decidable__lt_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_167970869__s17_from__string__aux_s6___main(obj*, obj*, obj*);
obj* _l_s5_rbmap_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__1(obj*, obj*);
obj* _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__2(obj*, obj*, obj*);
obj* _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__1;
obj* _l_s4_lean_s8_position_s7_has__lt;
obj* _l_s4_lean_s8_position_s13_decidable__lt_s6___main(obj*, obj*);
obj* _l_s4_lean_s8_position_s4_lean_s15_has__to__format(obj*);
obj* _l_s4_lean_s8_position_s13_decidable__eq(obj*, obj*);
obj* _l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__2;
obj* _l_s9___private_167970869__s17_from__string__aux(obj*, obj*, obj*);
obj* _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s8_position_s4_lean_s15_has__to__format_s9___spec__1(obj*);
obj* _l_s4_lean_s8_position_s2_lt_s6___main;
obj* _l_s4_lean_s8_position_s2_lt;
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(obj*, obj*, obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__3;
obj* _l_s4_lean_s9_file__map_s12_from__string(obj*);
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__2;
obj* _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s8_position_s13_decidable__lt(obj*, obj*);
obj* _l_s5_rbmap_s8_of__list_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__1(obj*);
obj* _l_s4_lean_s9_file__map_s12_to__position(obj*, obj*);
obj* _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(unsigned char, obj*);
obj* _l_s4_lean_s8_position_s13_decidable__eq(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_4;
obj* x_7;
obj* x_9;
obj* x_12;
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
obj* _init__l_s4_lean_s8_position_s2_lt_s6___main() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s8_position_s2_lt() {
{
obj* x_0;
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s8_position_s7_has__lt() {
{
obj* x_0;
x_0 = lean::box(0);
return x_0;
}
}
obj* _l_s4_lean_s8_position_s13_decidable__lt_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_4;
obj* x_7;
obj* x_9;
obj* x_12;
obj* x_13;
obj* x_14;
obj* x_15;
obj* x_20;
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
x_14 = _l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__1;
x_15 = _l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__2;
lean::inc(x_15);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_14);
x_20 = _l_s24_prod__has__decidable__lt_s6___rarg(x_14, x_14, x_15, x_15, x_12, x_13);
return x_20;
}
}
obj* _init__l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__1() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_dec_eq), 2, 0);
return x_0;
}
}
obj* _init__l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__2() {
{
obj* x_0;
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::nat_dec_lt), 2, 0);
return x_0;
}
}
obj* _l_s4_lean_s8_position_s13_decidable__lt(obj* x_0, obj* x_1) {
{
obj* x_2;
x_2 = _l_s4_lean_s8_position_s13_decidable__lt_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s8_position_s4_lean_s15_has__to__format(obj* x_0) {
{
obj* x_1;
obj* x_3;
obj* x_6;
unsigned char x_7;
obj* x_8;
obj* x_10;
obj* x_11;
obj* x_12;
obj* x_14;
obj* x_15;
obj* x_16;
obj* x_17;
obj* x_18;
obj* x_19;
obj* x_21;
obj* x_22;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s8_position_s4_lean_s15_has__to__format_s9___spec__1(x_1);
x_7 = 0;
x_8 = _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
x_11 = x_10;
x_12 = _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__2;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_7);
x_15 = x_14;
x_16 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s8_position_s4_lean_s15_has__to__format_s9___spec__1(x_3);
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_7);
x_18 = x_17;
x_19 = _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__3;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_7);
x_22 = x_21;
return x_22;
}
}
obj* _init__l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__1() {
{
obj* x_0;
obj* x_1;
x_0 = lean::mk_string("\x101\x	102\x97");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__2() {
{
obj* x_0;
obj* x_1;
x_0 = lean::mk_string(", ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__3() {
{
obj* x_0;
obj* x_1;
x_0 = lean::mk_string("\x101\x	102\x97	");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s8_position_s4_lean_s15_has__to__format_s9___spec__1(obj* x_0) {
{
obj* x_1;
obj* x_2;
x_1 = _l_s3_nat_s4_repr(x_0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s8_position_s9_inhabited() {
{
obj* x_0;
obj* x_1;
obj* x_2;
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s9___private_167970869__s17_from__string__aux_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
obj* x_4;
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6;
obj* x_7;
unsigned char x_9;
unsigned char x_11;
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
unsigned char x_18;
x_18 = 0;
x_9 = x_18;
goto lbl_10;
}
lbl_10:
{
unsigned x_19;
obj* x_20;
obj* x_21;
obj* x_22;
unsigned x_24;
x_19 = lean::string_iterator_curr(x_1);
x_20 = lean::mk_nat_obj(10u);
x_21 = lean::mk_nat_obj(55296u);
x_22 = lean::nat_dec_lt(x_20, x_21);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27;
obj* x_28;
lean::dec(x_22);
x_27 = lean::mk_nat_obj(57343u);
x_28 = lean::nat_dec_lt(x_27, x_20);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
unsigned x_32;
lean::dec(x_20);
lean::dec(x_28);
x_32 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_24 = x_32;
goto lbl_25;
}
else
{
obj* x_35;
obj* x_36;
lean::dec(x_28);
x_35 = lean::mk_nat_obj(1114112u);
x_36 = lean::nat_dec_lt(x_20, x_35);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
unsigned x_40;
lean::dec(x_20);
lean::dec(x_36);
x_40 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_24 = x_40;
goto lbl_25;
}
else
{
unsigned x_44;
lean::dec(x_3);
lean::dec(x_36);
x_44 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_24 = x_44;
goto lbl_25;
}
}
}
else
{
unsigned x_48;
lean::dec(x_22);
lean::dec(x_3);
x_48 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_24 = x_48;
goto lbl_25;
}
lbl_25:
{
obj* x_50;
obj* x_51;
obj* x_52;
x_50 = lean::box_uint32(x_19);
x_51 = lean::box_uint32(x_24);
x_52 = lean::nat_dec_eq(x_50, x_51);
lean::dec(x_51);
lean::dec(x_50);
if (lean::obj_tag(x_52) == 0)
{
obj* x_57;
obj* x_58;
lean::dec(x_52);
lean::dec(x_6);
x_57 = lean::string_iterator_next(x_1);
x_58 = _l_s9___private_167970869__s17_from__string__aux_s6___main(x_7, x_57, x_2);
return x_58;
}
else
{
obj* x_60;
obj* x_61;
obj* x_62;
obj* x_66;
obj* x_67;
obj* x_68;
lean::dec(x_52);
x_60 = lean::string_iterator_next(x_1);
x_61 = lean::string_iterator_offset(x_60);
x_62 = lean::nat_add(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
lean::inc(x_62);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_61);
lean::cnstr_set(x_66, 1, x_62);
x_67 = _l_s9___private_167970869__s17_from__string__aux_s6___main(x_7, x_60, x_62);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
obj* x_74;
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_74 = lean::box(0);
return x_74;
}
}
}
obj* _l_s9___private_167970869__s17_from__string__aux(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
x_3 = _l_s9___private_167970869__s17_from__string__aux_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s9_file__map_s12_from__string(obj* x_0) {
{
obj* x_1;
obj* x_2;
obj* x_3;
obj* x_4;
obj* x_5;
x_1 = lean::string_length(x_0);
x_2 = lean::string_mk_iterator(x_0);
x_3 = lean::mk_nat_obj(1u);
x_4 = _l_s9___private_167970869__s17_from__string__aux_s6___main(x_1, x_2, x_3);
x_5 = _l_s5_rbmap_s8_of__list_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__1(x_4);
return x_5;
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5;
obj* x_7;
obj* x_9;
obj* x_11;
obj* x_13;
obj* x_14;
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
obj* x_22;
obj* x_23;
lean::dec(x_16);
x_22 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_11, x_1, x_2);
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
obj* x_25;
obj* x_26;
lean::dec(x_14);
x_25 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_5, x_1, x_2);
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
obj* x_27;
obj* x_29;
obj* x_31;
obj* x_33;
obj* x_35;
obj* x_36;
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
x_45 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_33);
if (x_45 == 0)
{
obj* x_47;
obj* x_48;
lean::dec(x_35);
x_47 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_33, x_1, x_2);
x_48 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_47, x_29, x_31, x_27);
return x_48;
}
else
{
obj* x_49;
obj* x_50;
x_49 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_33, x_1, x_2);
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
x_53 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_27);
if (x_53 == 0)
{
obj* x_55;
obj* x_56;
lean::dec(x_35);
x_55 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_27, x_1, x_2);
x_56 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_55, x_29, x_31, x_33);
return x_56;
}
else
{
obj* x_57;
obj* x_58;
x_57 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_27, x_1, x_2);
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
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_4;
obj* x_5;
obj* x_6;
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__4(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3;
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__3(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s5_rbmap_s8_of__list_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__1(obj* x_0) {
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
obj* x_3;
obj* x_5;
obj* x_8;
obj* x_10;
obj* x_13;
obj* x_14;
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
x_13 = _l_s5_rbmap_s8_of__list_s6___main_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__1(x_5);
x_14 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s9_file__map_s12_from__string_s9___spec__3(x_13, x_8, x_10);
return x_14;
}
}
}
obj* _l_s4_lean_s9_file__map_s12_to__position(obj* x_0, obj* x_1) {
{
obj* x_3;
lean::inc(x_1);
x_3 = _l_s5_rbmap_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__1(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5;
obj* x_6;
lean::dec(x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
else
{
obj* x_7;
obj* x_10;
obj* x_12;
obj* x_15;
obj* x_18;
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
obj* _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5;
obj* x_7;
obj* x_9;
obj* x_11;
obj* x_14;
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
obj* x_22;
obj* x_23;
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
obj* x_25;
obj* x_26;
obj* x_27;
lean::dec(x_18);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(x_11, x_1, x_26);
return x_27;
}
}
else
{
obj* x_32;
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_14);
x_32 = _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(x_5, x_1, x_2);
return x_32;
}
}
default:
{
obj* x_33;
obj* x_35;
obj* x_37;
obj* x_39;
obj* x_42;
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
obj* x_50;
obj* x_51;
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
obj* x_53;
obj* x_54;
obj* x_55;
lean::dec(x_46);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_35);
lean::cnstr_set(x_53, 1, x_37);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(x_39, x_1, x_54);
return x_55;
}
}
else
{
obj* x_60;
lean::dec(x_42);
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_60 = _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(x_33, x_1, x_2);
return x_60;
}
}
}
}
}
obj* _l_s5_rbmap_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_2;
obj* x_3;
x_2 = lean::box(0);
x_3 = _l_s6_rbnode_s12_lower__bound_s6___main_s4___at_s4_lean_s9_file__map_s12_to__position_s9___spec__2(x_0, x_1, x_2);
return x_3;
}
}
void _l_initialize__l_s4_init_s4_data_s3_nat_s7_default();
void _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default();
void _l_initialize__l_s4_init_s4_lean_s6_format();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s8_position() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s7_default();
 _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default();
 _l_initialize__l_s4_init_s4_lean_s6_format();
 _l_s4_lean_s8_position_s2_lt_s6___main = _init__l_s4_lean_s8_position_s2_lt_s6___main();
 _l_s4_lean_s8_position_s2_lt = _init__l_s4_lean_s8_position_s2_lt();
 _l_s4_lean_s8_position_s7_has__lt = _init__l_s4_lean_s8_position_s7_has__lt();
 _l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__1 = _init__l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__1();
 _l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__2 = _init__l_s4_lean_s8_position_s13_decidable__lt_s6___main_s11___closed__2();
 _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__1 = _init__l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__1();
 _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__2 = _init__l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__2();
 _l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__3 = _init__l_s4_lean_s8_position_s4_lean_s15_has__to__format_s11___closed__3();
 _l_s4_lean_s8_position_s9_inhabited = _init__l_s4_lean_s8_position_s9_inhabited();
}

// Lean compiler output
// Module: init.data.int.basic
// Imports: init.data.nat.basic init.data.list.default init.coe init.data.repr init.data.to_string
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_int_div(obj*, obj*);
obj* l_int_repr___main___closed__1;
obj* l_int_lt;
obj* l_int_quot___main(obj*, obj*);
obj* l_int_sign___main(obj*);
obj* l_int_repr___main(obj*);
obj* l_int_le;
obj* l_int_neg___main(obj*);
obj* l_int_mod___main(obj*, obj*);
obj* l_int_to__nat(obj*);
obj* l_int_fdiv(obj*, obj*);
extern obj* l_true_decidable;
obj* l_int_div___main(obj*, obj*);
obj* l_int_has__neg;
obj* l___private_3285259795__dec__nonneg___main(obj*);
obj* l___private_1805987925__nonneg___main;
obj* l_int_nat__mod(obj*, obj*);
obj* l_int_sign(obj*);
obj* l_int_has__mod;
obj* l_int_add___main(obj*, obj*);
obj* l___private_3285259795__dec__nonneg(obj*);
obj* l_int_fmod(obj*, obj*);
obj* l_int_one;
obj* l_int_sub__nat__nat(obj*, obj*);
obj* l_int_rem___main(obj*, obj*);
obj* l_int_has__coe(obj*);
obj* l_int_has__one;
obj* l_int_zero;
obj* l_int_has__to__string;
obj* l_int_has__le;
obj* l___private_1805987925__nonneg;
obj* l_int_has__mul;
obj* l_int_neg__of__nat___main(obj*);
obj* l_int_fdiv___main(obj*, obj*);
obj* l_int_has__repr;
obj* l_nat_repr(obj*);
obj* l_int_sign___main___closed__1;
obj* l_int_nat__abs___main___closed__1;
obj* l_int_mul___main(obj*, obj*);
obj* l_int_has__sub;
obj* l_int_has__zero;
obj* l_int_has__div;
obj* l_int_mod(obj*, obj*);
obj* l_int_has__lt;
obj* l_int_repr(obj*);
obj* l_int_neg__of__nat(obj*);
obj* l_int_has__add;
obj* l_dec__eq(obj*, obj*);
obj* l_int_nat__abs___main(obj*);
obj* l_int_fmod___main(obj*, obj*);
obj* l_int_to__nat___main(obj*);
extern obj* l_false_decidable;
obj* l_int_has__coe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_int_nat__abs___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; 
lean::dec(x_2);
x_7 = lean::nat_abs(x_0);
lean::dec(x_0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_7, x_9);
lean::dec(x_7);
x_12 = lean::nat_add(x_10, x_9);
lean::dec(x_9);
lean::dec(x_10);
return x_12;
}
}
}
obj* _init_l_int_nat__abs___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_dec__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_11; 
lean::dec(x_5);
x_7 = lean::nat_abs(x_0);
lean::dec(x_0);
x_9 = lean::nat_abs(x_1);
lean::dec(x_1);
x_11 = lean::nat_dec_eq(x_7, x_9);
lean::dec(x_9);
lean::dec(x_7);
return x_11;
}
else
{
obj* x_17; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_17 = lean::box(0);
return x_17;
}
}
else
{
obj* x_19; 
lean::dec(x_3);
x_19 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_19);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_35; 
lean::dec(x_19);
x_25 = lean::nat_abs(x_0);
lean::dec(x_0);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_25, x_27);
lean::dec(x_25);
x_30 = lean::nat_abs(x_1);
lean::dec(x_1);
x_32 = lean::nat_sub(x_30, x_27);
lean::dec(x_27);
lean::dec(x_30);
x_35 = lean::nat_dec_eq(x_28, x_32);
lean::dec(x_32);
lean::dec(x_28);
return x_35;
}
}
}
}
obj* l_int_repr___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = l_nat_repr(x_4);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_19; 
lean::dec(x_2);
x_8 = lean::nat_abs(x_0);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_8, x_10);
lean::dec(x_8);
x_13 = lean::nat_add(x_11, x_10);
lean::dec(x_10);
lean::dec(x_11);
x_16 = l_nat_repr(x_13);
x_17 = l_int_repr___main___closed__1;
lean::inc(x_17);
x_19 = lean::string_append(x_17, x_16);
lean::dec(x_16);
return x_19;
}
}
}
obj* _init_l_int_repr___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* l_int_repr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_repr___main(x_0);
return x_1;
}
}
obj* _init_l_int_has__repr() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_repr), 1, 0);
return x_0;
}
}
obj* _init_l_int_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_repr), 1, 0);
return x_0;
}
}
obj* _init_l_int_zero() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_int_one() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_int_has__zero() {
_start:
{
obj* x_0; 
x_0 = l_int_zero;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_int_has__one() {
_start:
{
obj* x_0; 
x_0 = l_int_one;
lean::inc(x_0);
return x_0;
}
}
obj* l_int_neg__of__nat___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; obj* x_9; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_0, x_5);
lean::dec(x_5);
lean::dec(x_0);
x_9 = lean::int_neg_succ_of_nat(x_6);
lean::dec(x_6);
return x_9;
}
else
{
obj* x_13; 
lean::dec(x_0);
lean::dec(x_2);
x_13 = l_int_zero;
lean::inc(x_13);
return x_13;
}
}
}
obj* l_int_neg__of__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_neg__of__nat___main(x_0);
return x_1;
}
}
obj* l_int_sub__nat__nat(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::nat_sub(x_1, x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
x_13 = lean::int_neg_succ_of_nat(x_10);
lean::dec(x_10);
return x_13;
}
else
{
obj* x_17; obj* x_20; 
lean::dec(x_4);
lean::dec(x_2);
x_17 = lean::nat_sub(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
x_20 = lean::nat2int(x_17);
lean::dec(x_17);
return x_20;
}
}
}
obj* l_int_neg___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = l_int_neg__of__nat___main(x_4);
return x_6;
}
else
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_16; 
lean::dec(x_2);
x_8 = lean::nat_abs(x_0);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_8, x_10);
lean::dec(x_8);
x_13 = lean::nat_add(x_11, x_10);
lean::dec(x_10);
lean::dec(x_11);
x_16 = lean::nat2int(x_13);
lean::dec(x_13);
return x_16;
}
}
}
obj* l_int_add___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_14; 
lean::dec(x_7);
x_9 = lean::nat_abs(x_1);
lean::dec(x_1);
x_11 = lean::nat_add(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = lean::nat2int(x_11);
lean::dec(x_11);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; 
lean::dec(x_7);
x_17 = lean::nat_abs(x_1);
lean::dec(x_1);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_17, x_19);
lean::dec(x_17);
x_22 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_25 = l_int_sub__nat__nat(x_5, x_22);
return x_25;
}
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_3);
x_27 = lean::nat_abs(x_0);
lean::dec(x_0);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_sub(x_27, x_29);
lean::dec(x_27);
x_32 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_39; 
lean::dec(x_32);
x_34 = lean::nat_abs(x_1);
lean::dec(x_1);
x_36 = lean::nat_add(x_30, x_29);
lean::dec(x_29);
lean::dec(x_30);
x_39 = l_int_sub__nat__nat(x_34, x_36);
return x_39;
}
else
{
obj* x_41; obj* x_43; obj* x_45; obj* x_48; obj* x_51; 
lean::dec(x_32);
x_41 = lean::nat_abs(x_1);
lean::dec(x_1);
x_43 = lean::nat_sub(x_41, x_29);
lean::dec(x_41);
x_45 = lean::nat_add(x_30, x_43);
lean::dec(x_43);
lean::dec(x_30);
x_48 = lean::nat_add(x_45, x_29);
lean::dec(x_29);
lean::dec(x_45);
x_51 = lean::int_neg_succ_of_nat(x_48);
lean::dec(x_48);
return x_51;
}
}
}
}
obj* l_int_mul___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_14; 
lean::dec(x_7);
x_9 = lean::nat_abs(x_1);
lean::dec(x_1);
x_11 = lean::nat_mul(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = lean::nat2int(x_11);
lean::dec(x_11);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_28; 
lean::dec(x_7);
x_17 = lean::nat_abs(x_1);
lean::dec(x_1);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_17, x_19);
lean::dec(x_17);
x_22 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_25 = lean::nat_mul(x_5, x_22);
lean::dec(x_22);
lean::dec(x_5);
x_28 = l_int_neg__of__nat___main(x_25);
return x_28;
}
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_35; 
lean::dec(x_3);
x_30 = lean::nat_abs(x_0);
lean::dec(x_0);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::nat_sub(x_30, x_32);
lean::dec(x_30);
x_35 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_35) == 0)
{
obj* x_37; obj* x_39; obj* x_42; obj* x_45; 
lean::dec(x_35);
x_37 = lean::nat_abs(x_1);
lean::dec(x_1);
x_39 = lean::nat_add(x_33, x_32);
lean::dec(x_32);
lean::dec(x_33);
x_42 = lean::nat_mul(x_39, x_37);
lean::dec(x_37);
lean::dec(x_39);
x_45 = l_int_neg__of__nat___main(x_42);
return x_45;
}
else
{
obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_59; 
lean::dec(x_35);
x_47 = lean::nat_abs(x_1);
lean::dec(x_1);
x_49 = lean::nat_sub(x_47, x_32);
lean::dec(x_47);
x_51 = lean::nat_add(x_33, x_32);
lean::dec(x_33);
x_53 = lean::nat_add(x_49, x_32);
lean::dec(x_32);
lean::dec(x_49);
x_56 = lean::nat_mul(x_51, x_53);
lean::dec(x_53);
lean::dec(x_51);
x_59 = lean::nat2int(x_56);
lean::dec(x_56);
return x_59;
}
}
}
}
obj* _init_l_int_has__neg() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_neg), 1, 0);
return x_0;
}
}
obj* _init_l_int_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_add), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_mul), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_sub), 2, 0);
return x_0;
}
}
obj* l_int_sign___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
lean::dec(x_6);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; 
lean::dec(x_7);
x_11 = l_int_one;
lean::inc(x_11);
return x_11;
}
else
{
obj* x_14; 
lean::dec(x_7);
x_14 = l_int_zero;
lean::inc(x_14);
return x_14;
}
}
else
{
obj* x_18; 
lean::dec(x_0);
lean::dec(x_2);
x_18 = l_int_sign___main___closed__1;
lean::inc(x_18);
return x_18;
}
}
}
obj* _init_l_int_sign___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_int_one;
x_1 = lean::int_neg(x_0);
return x_1;
}
}
obj* l_int_sign(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_sign___main(x_0);
return x_1;
}
}
obj* l_int_div___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_14; 
lean::dec(x_7);
x_9 = lean::nat_abs(x_1);
lean::dec(x_1);
x_11 = lean::nat_div(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = lean::nat2int(x_11);
lean::dec(x_11);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_28; obj* x_30; 
lean::dec(x_7);
x_17 = lean::nat_abs(x_1);
lean::dec(x_1);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_17, x_19);
lean::dec(x_17);
x_22 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_25 = lean::nat_div(x_5, x_22);
lean::dec(x_22);
lean::dec(x_5);
x_28 = lean::nat2int(x_25);
lean::dec(x_25);
x_30 = lean::int_neg(x_28);
lean::dec(x_28);
return x_30;
}
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; 
lean::dec(x_3);
x_33 = lean::nat_abs(x_0);
lean::dec(x_0);
x_35 = lean::mk_nat_obj(1u);
x_36 = lean::nat_sub(x_33, x_35);
lean::dec(x_33);
x_38 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_38);
lean::dec(x_35);
x_41 = lean::nat_abs(x_1);
lean::dec(x_1);
x_43 = lean::mk_nat_obj(0u);
x_44 = lean::nat_dec_eq(x_41, x_43);
lean::dec(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_44);
x_47 = lean::nat_div(x_36, x_41);
lean::dec(x_41);
lean::dec(x_36);
x_50 = lean::int_neg_succ_of_nat(x_47);
lean::dec(x_47);
return x_50;
}
else
{
obj* x_55; 
lean::dec(x_41);
lean::dec(x_44);
lean::dec(x_36);
x_55 = l_int_zero;
lean::inc(x_55);
return x_55;
}
}
else
{
obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_67; obj* x_70; 
lean::dec(x_38);
x_58 = lean::nat_abs(x_1);
lean::dec(x_1);
x_60 = lean::nat_sub(x_58, x_35);
lean::dec(x_58);
x_62 = lean::nat_add(x_60, x_35);
lean::dec(x_60);
x_64 = lean::nat_div(x_36, x_62);
lean::dec(x_62);
lean::dec(x_36);
x_67 = lean::nat_add(x_64, x_35);
lean::dec(x_35);
lean::dec(x_64);
x_70 = lean::nat2int(x_67);
lean::dec(x_67);
return x_70;
}
}
}
}
obj* l_int_div(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_int_div___main(x_0, x_1);
return x_2;
}
}
obj* l_int_mod___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_12; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_mod(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
x_12 = lean::nat2int(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_27; 
lean::dec(x_3);
x_15 = lean::nat_abs(x_0);
lean::dec(x_0);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_15, x_17);
lean::dec(x_15);
x_20 = lean::nat_abs(x_1);
lean::dec(x_1);
x_22 = lean::nat_mod(x_18, x_20);
lean::dec(x_18);
x_24 = lean::nat_add(x_22, x_17);
lean::dec(x_17);
lean::dec(x_22);
x_27 = l_int_sub__nat__nat(x_20, x_24);
return x_27;
}
}
}
obj* l_int_mod(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_int_mod___main(x_0, x_1);
return x_2;
}
}
obj* l_int_fdiv___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_5, x_7);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; 
lean::dec(x_8);
x_11 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_18; 
lean::dec(x_11);
x_13 = lean::nat_abs(x_1);
lean::dec(x_1);
x_15 = lean::nat_div(x_5, x_13);
lean::dec(x_13);
lean::dec(x_5);
x_18 = lean::nat2int(x_15);
lean::dec(x_15);
return x_18;
}
else
{
obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_31; obj* x_34; 
lean::dec(x_11);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_sub(x_5, x_21);
lean::dec(x_5);
x_24 = lean::nat_abs(x_1);
lean::dec(x_1);
x_26 = lean::nat_sub(x_24, x_21);
lean::dec(x_24);
x_28 = lean::nat_add(x_26, x_21);
lean::dec(x_21);
lean::dec(x_26);
x_31 = lean::nat_div(x_22, x_28);
lean::dec(x_28);
lean::dec(x_22);
x_34 = lean::int_neg_succ_of_nat(x_31);
lean::dec(x_31);
return x_34;
}
}
else
{
obj* x_39; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_1);
x_39 = l_int_zero;
lean::inc(x_39);
return x_39;
}
}
else
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_3);
x_42 = lean::nat_abs(x_0);
lean::dec(x_0);
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_sub(x_42, x_44);
lean::dec(x_42);
x_47 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_47);
lean::dec(x_44);
x_50 = lean::nat_abs(x_1);
lean::dec(x_1);
x_52 = lean::mk_nat_obj(0u);
x_53 = lean::nat_dec_eq(x_50, x_52);
lean::dec(x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_56; obj* x_59; 
lean::dec(x_53);
x_56 = lean::nat_div(x_45, x_50);
lean::dec(x_50);
lean::dec(x_45);
x_59 = lean::int_neg_succ_of_nat(x_56);
lean::dec(x_56);
return x_59;
}
else
{
obj* x_64; 
lean::dec(x_45);
lean::dec(x_50);
lean::dec(x_53);
x_64 = l_int_zero;
lean::inc(x_64);
return x_64;
}
}
else
{
obj* x_67; obj* x_69; obj* x_71; obj* x_73; obj* x_76; obj* x_79; 
lean::dec(x_47);
x_67 = lean::nat_abs(x_1);
lean::dec(x_1);
x_69 = lean::nat_sub(x_67, x_44);
lean::dec(x_67);
x_71 = lean::nat_add(x_45, x_44);
lean::dec(x_45);
x_73 = lean::nat_add(x_69, x_44);
lean::dec(x_44);
lean::dec(x_69);
x_76 = lean::nat_div(x_71, x_73);
lean::dec(x_73);
lean::dec(x_71);
x_79 = lean::nat2int(x_76);
lean::dec(x_76);
return x_79;
}
}
}
}
obj* l_int_fdiv(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_int_fdiv___main(x_0, x_1);
return x_2;
}
}
obj* l_int_fmod___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_5, x_7);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; 
lean::dec(x_8);
x_11 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_18; 
lean::dec(x_11);
x_13 = lean::nat_abs(x_1);
lean::dec(x_1);
x_15 = lean::nat_mod(x_5, x_13);
lean::dec(x_13);
lean::dec(x_5);
x_18 = lean::nat2int(x_15);
lean::dec(x_15);
return x_18;
}
else
{
obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_33; 
lean::dec(x_11);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_sub(x_5, x_21);
lean::dec(x_5);
x_24 = lean::nat_abs(x_1);
lean::dec(x_1);
x_26 = lean::nat_sub(x_24, x_21);
lean::dec(x_24);
x_28 = lean::nat_add(x_26, x_21);
lean::dec(x_21);
x_30 = lean::nat_mod(x_22, x_28);
lean::dec(x_28);
lean::dec(x_22);
x_33 = l_int_sub__nat__nat(x_30, x_26);
return x_33;
}
}
else
{
obj* x_37; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_1);
x_37 = l_int_zero;
lean::inc(x_37);
return x_37;
}
}
else
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_3);
x_40 = lean::nat_abs(x_0);
lean::dec(x_0);
x_42 = lean::mk_nat_obj(1u);
x_43 = lean::nat_sub(x_40, x_42);
lean::dec(x_40);
x_45 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_45) == 0)
{
obj* x_47; obj* x_49; obj* x_51; obj* x_54; 
lean::dec(x_45);
x_47 = lean::nat_abs(x_1);
lean::dec(x_1);
x_49 = lean::nat_mod(x_43, x_47);
lean::dec(x_43);
x_51 = lean::nat_add(x_49, x_42);
lean::dec(x_42);
lean::dec(x_49);
x_54 = l_int_sub__nat__nat(x_47, x_51);
return x_54;
}
else
{
obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_65; obj* x_68; obj* x_70; 
lean::dec(x_45);
x_56 = lean::nat_abs(x_1);
lean::dec(x_1);
x_58 = lean::nat_sub(x_56, x_42);
lean::dec(x_56);
x_60 = lean::nat_add(x_43, x_42);
lean::dec(x_43);
x_62 = lean::nat_add(x_58, x_42);
lean::dec(x_42);
lean::dec(x_58);
x_65 = lean::nat_mod(x_60, x_62);
lean::dec(x_62);
lean::dec(x_60);
x_68 = lean::nat2int(x_65);
lean::dec(x_65);
x_70 = lean::int_neg(x_68);
lean::dec(x_68);
return x_70;
}
}
}
}
obj* l_int_fmod(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_int_fmod___main(x_0, x_1);
return x_2;
}
}
obj* l_int_quot___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_14; 
lean::dec(x_7);
x_9 = lean::nat_abs(x_1);
lean::dec(x_1);
x_11 = lean::nat_div(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = lean::nat2int(x_11);
lean::dec(x_11);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_28; obj* x_30; 
lean::dec(x_7);
x_17 = lean::nat_abs(x_1);
lean::dec(x_1);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_17, x_19);
lean::dec(x_17);
x_22 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_25 = lean::nat_div(x_5, x_22);
lean::dec(x_22);
lean::dec(x_5);
x_28 = lean::nat2int(x_25);
lean::dec(x_25);
x_30 = lean::int_neg(x_28);
lean::dec(x_28);
return x_30;
}
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; 
lean::dec(x_3);
x_33 = lean::nat_abs(x_0);
lean::dec(x_0);
x_35 = lean::mk_nat_obj(1u);
x_36 = lean::nat_sub(x_33, x_35);
lean::dec(x_33);
x_38 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_42; obj* x_45; obj* x_48; obj* x_50; 
lean::dec(x_38);
x_40 = lean::nat_abs(x_1);
lean::dec(x_1);
x_42 = lean::nat_add(x_36, x_35);
lean::dec(x_35);
lean::dec(x_36);
x_45 = lean::nat_div(x_42, x_40);
lean::dec(x_40);
lean::dec(x_42);
x_48 = lean::nat2int(x_45);
lean::dec(x_45);
x_50 = lean::int_neg(x_48);
lean::dec(x_48);
return x_50;
}
else
{
obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_62; obj* x_65; 
lean::dec(x_38);
x_53 = lean::nat_abs(x_1);
lean::dec(x_1);
x_55 = lean::nat_sub(x_53, x_35);
lean::dec(x_53);
x_57 = lean::nat_add(x_36, x_35);
lean::dec(x_36);
x_59 = lean::nat_add(x_55, x_35);
lean::dec(x_35);
lean::dec(x_55);
x_62 = lean::nat_div(x_57, x_59);
lean::dec(x_59);
lean::dec(x_57);
x_65 = lean::nat2int(x_62);
lean::dec(x_62);
return x_65;
}
}
}
}
obj* l_int_rem___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_3);
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_14; 
lean::dec(x_7);
x_9 = lean::nat_abs(x_1);
lean::dec(x_1);
x_11 = lean::nat_mod(x_5, x_9);
lean::dec(x_9);
lean::dec(x_5);
x_14 = lean::nat2int(x_11);
lean::dec(x_11);
return x_14;
}
else
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_28; 
lean::dec(x_7);
x_17 = lean::nat_abs(x_1);
lean::dec(x_1);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_17, x_19);
lean::dec(x_17);
x_22 = lean::nat_add(x_20, x_19);
lean::dec(x_19);
lean::dec(x_20);
x_25 = lean::nat_mod(x_5, x_22);
lean::dec(x_22);
lean::dec(x_5);
x_28 = lean::nat2int(x_25);
lean::dec(x_25);
return x_28;
}
}
else
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; 
lean::dec(x_3);
x_31 = lean::nat_abs(x_0);
lean::dec(x_0);
x_33 = lean::mk_nat_obj(1u);
x_34 = lean::nat_sub(x_31, x_33);
lean::dec(x_31);
x_36 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_40; obj* x_43; obj* x_46; obj* x_48; 
lean::dec(x_36);
x_38 = lean::nat_abs(x_1);
lean::dec(x_1);
x_40 = lean::nat_add(x_34, x_33);
lean::dec(x_33);
lean::dec(x_34);
x_43 = lean::nat_mod(x_40, x_38);
lean::dec(x_38);
lean::dec(x_40);
x_46 = lean::nat2int(x_43);
lean::dec(x_43);
x_48 = lean::int_neg(x_46);
lean::dec(x_46);
return x_48;
}
else
{
obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_60; obj* x_63; obj* x_65; 
lean::dec(x_36);
x_51 = lean::nat_abs(x_1);
lean::dec(x_1);
x_53 = lean::nat_sub(x_51, x_33);
lean::dec(x_51);
x_55 = lean::nat_add(x_34, x_33);
lean::dec(x_34);
x_57 = lean::nat_add(x_53, x_33);
lean::dec(x_33);
lean::dec(x_53);
x_60 = lean::nat_mod(x_55, x_57);
lean::dec(x_57);
lean::dec(x_55);
x_63 = lean::nat2int(x_60);
lean::dec(x_60);
x_65 = lean::int_neg(x_63);
lean::dec(x_63);
return x_65;
}
}
}
}
obj* _init_l_int_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_div), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_mod), 2, 0);
return x_0;
}
}
obj* l_int_to__nat___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(0u);
return x_8;
}
}
}
obj* l_int_to__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_int_to__nat___main(x_0);
return x_1;
}
}
obj* l_int_nat__mod(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_int_mod___main(x_0, x_1);
x_3 = l_int_to__nat___main(x_2);
return x_3;
}
}
obj* _init_l___private_1805987925__nonneg___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l___private_1805987925__nonneg() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_int_le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_int_has__le() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_int_lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_int_has__lt() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l___private_3285259795__dec__nonneg___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = l_true_decidable;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = l_false_decidable;
lean::inc(x_8);
return x_8;
}
}
}
obj* l___private_3285259795__dec__nonneg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_3285259795__dec__nonneg___main(x_0);
return x_1;
}
}
void initialize_init_data_nat_basic();
void initialize_init_data_list_default();
void initialize_init_coe();
void initialize_init_data_repr();
void initialize_init_data_to__string();
static bool _G_initialized = false;
void initialize_init_data_int_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
 initialize_init_data_list_default();
 initialize_init_coe();
 initialize_init_data_repr();
 initialize_init_data_to__string();
 l_int_nat__abs___main___closed__1 = _init_l_int_nat__abs___main___closed__1();
 l_int_repr___main___closed__1 = _init_l_int_repr___main___closed__1();
 l_int_has__repr = _init_l_int_has__repr();
 l_int_has__to__string = _init_l_int_has__to__string();
 l_int_zero = _init_l_int_zero();
 l_int_one = _init_l_int_one();
 l_int_has__zero = _init_l_int_has__zero();
 l_int_has__one = _init_l_int_has__one();
 l_int_has__neg = _init_l_int_has__neg();
 l_int_has__add = _init_l_int_has__add();
 l_int_has__mul = _init_l_int_has__mul();
 l_int_has__sub = _init_l_int_has__sub();
 l_int_sign___main___closed__1 = _init_l_int_sign___main___closed__1();
 l_int_has__div = _init_l_int_has__div();
 l_int_has__mod = _init_l_int_has__mod();
 l___private_1805987925__nonneg___main = _init_l___private_1805987925__nonneg___main();
 l___private_1805987925__nonneg = _init_l___private_1805987925__nonneg();
 l_int_le = _init_l_int_le();
 l_int_has__le = _init_l_int_has__le();
 l_int_lt = _init_l_int_lt();
 l_int_has__lt = _init_l_int_has__lt();
}

// Lean compiler output
// Module: init.data.int.basic
// Imports: init.data.nat.basic init.data.list.default init.coe init.data.repr init.data.to_string
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s3_int_s3_div(obj*, obj*);
obj* _l_s3_int_s4_repr_s6___main_s11___closed__1;
obj* _l_s3_int_s2_lt;
obj* _l_s3_int_s4_quot_s6___main(obj*, obj*);
obj* _l_s3_int_s4_sign_s6___main(obj*);
obj* _l_s3_int_s4_repr_s6___main(obj*);
obj* _l_s3_int_s2_le;
obj* _l_s3_int_s3_neg_s6___main(obj*);
obj* _l_s3_int_s3_mod_s6___main(obj*, obj*);
obj* _l_s3_int_s7_to__nat(obj*);
obj* _l_s3_int_s4_fdiv(obj*, obj*);
obj* _l_s4_true_s9_decidable;
obj* _l_s3_int_s3_div_s6___main(obj*, obj*);
obj* _l_s3_int_s8_has__neg;
obj* _l_s9___private_3285259795__s11_dec__nonneg_s6___main(obj*);
obj* _l_s9___private_1805987925__s6_nonneg_s6___main;
obj* _l_s3_int_s8_nat__mod(obj*, obj*);
obj* _l_s3_int_s4_sign(obj*);
obj* _l_s3_int_s8_has__mod;
obj* _l_s3_int_s3_add_s6___main(obj*, obj*);
obj* _l_s9___private_3285259795__s11_dec__nonneg(obj*);
obj* _l_s3_int_s4_fmod(obj*, obj*);
obj* _l_s3_int_s3_one;
obj* _l_s3_int_s13_sub__nat__nat(obj*, obj*);
obj* _l_s3_int_s3_rem_s6___main(obj*, obj*);
obj* _l_s3_int_s8_has__coe(obj*);
obj* _l_s3_int_s8_has__one;
obj* _l_s3_int_s4_zero;
obj* _l_s3_int_s15_has__to__string;
obj* _l_s3_int_s7_has__le;
obj* _l_s9___private_1805987925__s6_nonneg;
obj* _l_s3_int_s8_has__mul;
obj* _l_s3_int_s12_neg__of__nat_s6___main(obj*);
obj* _l_s3_int_s4_fdiv_s6___main(obj*, obj*);
obj* _l_s3_int_s9_has__repr;
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s3_int_s4_sign_s6___main_s11___closed__1;
obj* _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
obj* _l_s3_int_s3_mul_s6___main(obj*, obj*);
obj* _l_s3_int_s8_has__sub;
obj* _l_s3_int_s9_has__zero;
obj* _l_s3_int_s8_has__div;
obj* _l_s3_int_s3_mod(obj*, obj*);
obj* _l_s3_int_s7_has__lt;
obj* _l_s3_int_s4_repr(obj*);
obj* _l_s3_int_s12_neg__of__nat(obj*);
obj* _l_s3_int_s8_has__add;
obj* _l_s7_dec__eq(obj*, obj*);
obj* _l_s3_int_s8_nat__abs_s6___main(obj*);
obj* _l_s3_int_s4_fmod_s6___main(obj*, obj*);
obj* _l_s3_int_s7_to__nat_s6___main(obj*);
obj* _l_s5_false_s9_decidable;
obj* _l_s3_int_s8_has__coe(obj* x_0) {
{
obj* x_1; 
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s3_int_s8_nat__abs_s6___main(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
obj* _init__l_s3_int_s8_nat__abs_s6___main_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s7_dec__eq(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_17 = lean::alloc_cnstr(0, 0, 0);
;
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
x_23 = lean::alloc_cnstr(0, 0, 0);
;
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
obj* _l_s3_int_s4_repr_s6___main(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = _l_s3_nat_s4_repr(x_4);
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
x_16 = _l_s3_nat_s4_repr(x_13);
x_17 = _l_s3_int_s4_repr_s6___main_s11___closed__1;
lean::inc(x_17);
x_19 = lean::string_append(x_17, x_16);
lean::dec(x_16);
return x_19;
}
}
}
obj* _init__l_s3_int_s4_repr_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* _l_s3_int_s4_repr(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s3_int_s4_repr_s6___main(x_0);
return x_1;
}
}
obj* _init__l_s3_int_s9_has__repr() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_int_s4_repr), 1, 0);
return x_0;
}
}
obj* _init__l_s3_int_s15_has__to__string() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_int_s4_repr), 1, 0);
return x_0;
}
}
obj* _init__l_s3_int_s4_zero() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s3_int_s3_one() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::nat2int(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s3_int_s9_has__zero() {
{
obj* x_0; 
x_0 = _l_s3_int_s4_zero;
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_int_s8_has__one() {
{
obj* x_0; 
x_0 = _l_s3_int_s3_one;
lean::inc(x_0);
return x_0;
}
}
obj* _l_s3_int_s12_neg__of__nat_s6___main(obj* x_0) {
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
x_13 = _l_s3_int_s4_zero;
lean::inc(x_13);
return x_13;
}
}
}
obj* _l_s3_int_s12_neg__of__nat(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s3_int_s12_neg__of__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s3_int_s13_sub__nat__nat(obj* x_0, obj* x_1) {
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
obj* _l_s3_int_s3_neg_s6___main(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; 
lean::dec(x_2);
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = _l_s3_int_s12_neg__of__nat_s6___main(x_4);
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
obj* _l_s3_int_s3_add_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_25 = _l_s3_int_s13_sub__nat__nat(x_5, x_22);
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
x_39 = _l_s3_int_s13_sub__nat__nat(x_34, x_36);
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
obj* _l_s3_int_s3_mul_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_28 = _l_s3_int_s12_neg__of__nat_s6___main(x_25);
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
x_45 = _l_s3_int_s12_neg__of__nat_s6___main(x_42);
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
obj* _init__l_s3_int_s8_has__neg() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_neg), 1, 0);
return x_0;
}
}
obj* _init__l_s3_int_s8_has__add() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_add), 2, 0);
return x_0;
}
}
obj* _init__l_s3_int_s8_has__mul() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_mul), 2, 0);
return x_0;
}
}
obj* _init__l_s3_int_s8_has__sub() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::int_sub), 2, 0);
return x_0;
}
}
obj* _l_s3_int_s4_sign_s6___main(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_11 = _l_s3_int_s3_one;
lean::inc(x_11);
return x_11;
}
else
{
obj* x_14; 
lean::dec(x_7);
x_14 = _l_s3_int_s4_zero;
lean::inc(x_14);
return x_14;
}
}
else
{
obj* x_18; 
lean::dec(x_0);
lean::dec(x_2);
x_18 = _l_s3_int_s4_sign_s6___main_s11___closed__1;
lean::inc(x_18);
return x_18;
}
}
}
obj* _init__l_s3_int_s4_sign_s6___main_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = _l_s3_int_s3_one;
x_1 = lean::int_neg(x_0);
return x_1;
}
}
obj* _l_s3_int_s4_sign(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s3_int_s4_sign_s6___main(x_0);
return x_1;
}
}
obj* _l_s3_int_s3_div_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_55 = _l_s3_int_s4_zero;
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
obj* _l_s3_int_s3_div(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s3_int_s3_div_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s3_int_s3_mod_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_27 = _l_s3_int_s13_sub__nat__nat(x_20, x_24);
return x_27;
}
}
}
obj* _l_s3_int_s3_mod(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s3_int_s3_mod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s3_int_s4_fdiv_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
obj* x_40; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_40 = _l_s3_int_s4_zero;
lean::inc(x_40);
return x_40;
}
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; 
lean::dec(x_3);
x_43 = lean::nat_abs(x_0);
lean::dec(x_0);
x_45 = lean::mk_nat_obj(1u);
x_46 = lean::nat_sub(x_43, x_45);
lean::dec(x_43);
x_48 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_48) == 0)
{
obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_48);
lean::dec(x_45);
x_51 = lean::nat_abs(x_1);
lean::dec(x_1);
x_53 = lean::mk_nat_obj(0u);
x_54 = lean::nat_dec_eq(x_51, x_53);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; obj* x_60; 
lean::dec(x_54);
x_57 = lean::nat_div(x_46, x_51);
lean::dec(x_51);
lean::dec(x_46);
x_60 = lean::int_neg_succ_of_nat(x_57);
lean::dec(x_57);
return x_60;
}
else
{
obj* x_65; 
lean::dec(x_46);
lean::dec(x_51);
lean::dec(x_54);
x_65 = _l_s3_int_s4_zero;
lean::inc(x_65);
return x_65;
}
}
else
{
obj* x_68; obj* x_70; obj* x_72; obj* x_74; obj* x_77; obj* x_80; 
lean::dec(x_48);
x_68 = lean::nat_abs(x_1);
lean::dec(x_1);
x_70 = lean::nat_sub(x_68, x_45);
lean::dec(x_68);
x_72 = lean::nat_add(x_46, x_45);
lean::dec(x_46);
x_74 = lean::nat_add(x_70, x_45);
lean::dec(x_45);
lean::dec(x_70);
x_77 = lean::nat_div(x_72, x_74);
lean::dec(x_74);
lean::dec(x_72);
x_80 = lean::nat2int(x_77);
lean::dec(x_77);
return x_80;
}
}
}
}
obj* _l_s3_int_s4_fdiv(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s3_int_s4_fdiv_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s3_int_s4_fmod_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
x_33 = _l_s3_int_s13_sub__nat__nat(x_30, x_26);
return x_33;
}
}
else
{
obj* x_38; 
lean::dec(x_5);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_38 = _l_s3_int_s4_zero;
lean::inc(x_38);
return x_38;
}
}
else
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; 
lean::dec(x_3);
x_41 = lean::nat_abs(x_0);
lean::dec(x_0);
x_43 = lean::mk_nat_obj(1u);
x_44 = lean::nat_sub(x_41, x_43);
lean::dec(x_41);
x_46 = lean::int_dec_lt(x_1, x_2);
if (lean::obj_tag(x_46) == 0)
{
obj* x_48; obj* x_50; obj* x_52; obj* x_55; 
lean::dec(x_46);
x_48 = lean::nat_abs(x_1);
lean::dec(x_1);
x_50 = lean::nat_mod(x_44, x_48);
lean::dec(x_44);
x_52 = lean::nat_add(x_50, x_43);
lean::dec(x_43);
lean::dec(x_50);
x_55 = _l_s3_int_s13_sub__nat__nat(x_48, x_52);
return x_55;
}
else
{
obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_69; obj* x_71; 
lean::dec(x_46);
x_57 = lean::nat_abs(x_1);
lean::dec(x_1);
x_59 = lean::nat_sub(x_57, x_43);
lean::dec(x_57);
x_61 = lean::nat_add(x_44, x_43);
lean::dec(x_44);
x_63 = lean::nat_add(x_59, x_43);
lean::dec(x_43);
lean::dec(x_59);
x_66 = lean::nat_mod(x_61, x_63);
lean::dec(x_63);
lean::dec(x_61);
x_69 = lean::nat2int(x_66);
lean::dec(x_66);
x_71 = lean::int_neg(x_69);
lean::dec(x_69);
return x_71;
}
}
}
}
obj* _l_s3_int_s4_fmod(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s3_int_s4_fmod_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s3_int_s4_quot_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
obj* _l_s3_int_s3_rem_s6___main(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
obj* _init__l_s3_int_s8_has__div() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_int_s3_div), 2, 0);
return x_0;
}
}
obj* _init__l_s3_int_s8_has__mod() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_int_s3_mod), 2, 0);
return x_0;
}
}
obj* _l_s3_int_s7_to__nat_s6___main(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
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
obj* _l_s3_int_s7_to__nat(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s3_int_s7_to__nat_s6___main(x_0);
return x_1;
}
}
obj* _l_s3_int_s8_nat__mod(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = _l_s3_int_s3_mod_s6___main(x_0, x_1);
x_3 = _l_s3_int_s7_to__nat_s6___main(x_2);
return x_3;
}
}
obj* _init__l_s9___private_1805987925__s6_nonneg_s6___main() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s9___private_1805987925__s6_nonneg() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_int_s2_le() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_int_s7_has__le() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _init__l_s3_int_s2_lt() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s3_int_s7_has__lt() {
{
obj* x_0; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
return x_0;
}
}
obj* _l_s9___private_3285259795__s11_dec__nonneg_s6___main(obj* x_0) {
{
obj* x_1; obj* x_2; 
x_1 = _l_s3_int_s8_nat__abs_s6___main_s11___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = _l_s4_true_s9_decidable;
lean::inc(x_5);
return x_5;
}
else
{
obj* x_8; 
lean::dec(x_2);
x_8 = _l_s5_false_s9_decidable;
lean::inc(x_8);
return x_8;
}
}
}
obj* _l_s9___private_3285259795__s11_dec__nonneg(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s9___private_3285259795__s11_dec__nonneg_s6___main(x_0);
return x_1;
}
}
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
void _l_initialize__l_s4_init_s4_data_s4_list_s7_default();
void _l_initialize__l_s4_init_s3_coe();
void _l_initialize__l_s4_init_s4_data_s4_repr();
void _l_initialize__l_s4_init_s4_data_s10_to__string();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s3_int_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
 _l_initialize__l_s4_init_s4_data_s4_list_s7_default();
 _l_initialize__l_s4_init_s3_coe();
 _l_initialize__l_s4_init_s4_data_s4_repr();
 _l_initialize__l_s4_init_s4_data_s10_to__string();
 _l_s3_int_s8_nat__abs_s6___main_s11___closed__1 = _init__l_s3_int_s8_nat__abs_s6___main_s11___closed__1();
 _l_s3_int_s4_repr_s6___main_s11___closed__1 = _init__l_s3_int_s4_repr_s6___main_s11___closed__1();
 _l_s3_int_s9_has__repr = _init__l_s3_int_s9_has__repr();
 _l_s3_int_s15_has__to__string = _init__l_s3_int_s15_has__to__string();
 _l_s3_int_s4_zero = _init__l_s3_int_s4_zero();
 _l_s3_int_s3_one = _init__l_s3_int_s3_one();
 _l_s3_int_s9_has__zero = _init__l_s3_int_s9_has__zero();
 _l_s3_int_s8_has__one = _init__l_s3_int_s8_has__one();
 _l_s3_int_s8_has__neg = _init__l_s3_int_s8_has__neg();
 _l_s3_int_s8_has__add = _init__l_s3_int_s8_has__add();
 _l_s3_int_s8_has__mul = _init__l_s3_int_s8_has__mul();
 _l_s3_int_s8_has__sub = _init__l_s3_int_s8_has__sub();
 _l_s3_int_s4_sign_s6___main_s11___closed__1 = _init__l_s3_int_s4_sign_s6___main_s11___closed__1();
 _l_s3_int_s8_has__div = _init__l_s3_int_s8_has__div();
 _l_s3_int_s8_has__mod = _init__l_s3_int_s8_has__mod();
 _l_s9___private_1805987925__s6_nonneg_s6___main = _init__l_s9___private_1805987925__s6_nonneg_s6___main();
 _l_s9___private_1805987925__s6_nonneg = _init__l_s9___private_1805987925__s6_nonneg();
 _l_s3_int_s2_le = _init__l_s3_int_s2_le();
 _l_s3_int_s7_has__le = _init__l_s3_int_s7_has__le();
 _l_s3_int_s2_lt = _init__l_s3_int_s2_lt();
 _l_s3_int_s7_has__lt = _init__l_s3_int_s7_has__lt();
}

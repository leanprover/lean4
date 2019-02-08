// Lean compiler output
// Module: init.data.int.basic
// Imports: init.data.nat.basic init.data.list.default init.coe init.data.repr init.data.to_string
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
obj* l_int_repr(obj*);
obj* l_int_has__repr;
uint8 l_dec__eq(obj*, obj*);
obj* l_int_neg__of__nat(obj*);
obj* l___private_3285259795__dec__nonneg___boxed(obj*);
extern uint8 l_true_decidable;
obj* l_int_fdiv___main(obj*, obj*);
obj* l_int_has__sub;
obj* l_int_mul___main(obj*, obj*);
obj* l_int_nat__abs___main(obj*);
extern uint8 l_false_decidable;
obj* l_int_repr___main(obj*);
obj* l_int_mod(obj*, obj*);
obj* l___private_1805987925__nonneg;
obj* l_int_to__nat___main(obj*);
obj* l_int_nat__abs___main___closed__1;
obj* l_int_quot___main(obj*, obj*);
obj* l___private_3285259795__dec__nonneg___main___boxed(obj*);
obj* l_int_has__mul;
obj* l___private_1805987925__nonneg___main;
obj* l_int_lt;
obj* l_int_neg__of__nat___main(obj*);
obj* l_int_has__lt;
obj* l_int_add___main(obj*, obj*);
obj* l_int_sub__nat__nat(obj*, obj*);
obj* l_int_dec__lt___boxed(obj*, obj*);
obj* l_int_zero;
obj* l_int_has__div;
obj* l_int_div___main(obj*, obj*);
uint8 l___private_3285259795__dec__nonneg___main(obj*);
obj* l_int_has__mod;
obj* l_int_sign(obj*);
obj* l_int_repr___main___closed__1;
obj* l_int_to__nat(obj*);
obj* l_int_has__coe(obj*);
obj* l_int_has__le;
obj* l_int_has__one;
obj* l_int_div(obj*, obj*);
obj* l_int_fdiv(obj*, obj*);
obj* l_dec__eq___boxed(obj*, obj*);
obj* l_int_neg___main(obj*);
obj* l_int_nat__mod(obj*, obj*);
uint8 l___private_3285259795__dec__nonneg(obj*);
obj* l_int_has__neg;
obj* l_int_fmod___main(obj*, obj*);
obj* l_int_fmod(obj*, obj*);
obj* l_int_rem___main(obj*, obj*);
obj* l_int_has__to__string;
obj* l_int_mod___main(obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_int_sign___main(obj*);
obj* l_int_has__add;
obj* l_int_le;
obj* l_int_has__zero;
obj* l_int_dec__le___boxed(obj*, obj*);
obj* l_int_sign___main___closed__1;
obj* l_int_one;
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
obj* x_1; uint8 x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; 
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_5, x_7);
lean::dec(x_5);
x_10 = lean::nat_add(x_8, x_7);
lean::dec(x_7);
lean::dec(x_8);
return x_10;
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
uint8 l_dec__eq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = lean::int_dec_lt(x_1, x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_7; uint8 x_9; 
x_5 = lean::nat_abs(x_0);
lean::dec(x_0);
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_dec_eq(x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
if (x_9 == 0)
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8 x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = 0;
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = lean::int_dec_lt(x_1, x_2);
if (x_17 == 0)
{
uint8 x_20; 
lean::dec(x_1);
lean::dec(x_0);
x_20 = 0;
return x_20;
}
else
{
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_28; uint8 x_31; 
x_21 = lean::nat_abs(x_0);
lean::dec(x_0);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_sub(x_21, x_23);
lean::dec(x_21);
x_26 = lean::nat_abs(x_1);
lean::dec(x_1);
x_28 = lean::nat_sub(x_26, x_23);
lean::dec(x_23);
lean::dec(x_26);
x_31 = lean::nat_dec_eq(x_24, x_28);
lean::dec(x_28);
lean::dec(x_24);
if (x_31 == 0)
{
uint8 x_34; 
x_34 = 0;
return x_34;
}
else
{
uint8 x_35; 
x_35 = 1;
return x_35;
}
}
}
}
}
obj* l_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_dec__eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_int_repr___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_5; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
x_5 = l_nat_repr(x_3);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_17; 
x_6 = lean::nat_abs(x_0);
lean::dec(x_0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_6, x_8);
lean::dec(x_6);
x_11 = lean::nat_add(x_9, x_8);
lean::dec(x_8);
lean::dec(x_9);
x_14 = l_nat_repr(x_11);
x_15 = l_int_repr___main___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
return x_17;
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
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
lean::dec(x_1);
if (x_2 == 0)
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_0, x_4);
lean::dec(x_4);
lean::dec(x_0);
x_8 = lean::int_neg_succ_of_nat(x_5);
lean::dec(x_5);
return x_8;
}
else
{
obj* x_11; 
lean::dec(x_0);
x_11 = l_int_zero;
lean::inc(x_11);
return x_11;
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
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::nat_sub(x_1, x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_8; obj* x_9; obj* x_12; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_2, x_8);
lean::dec(x_8);
lean::dec(x_2);
x_12 = lean::int_neg_succ_of_nat(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_15; obj* x_18; 
lean::dec(x_2);
x_15 = lean::nat_sub(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
x_18 = lean::nat2int(x_15);
lean::dec(x_15);
return x_18;
}
}
}
obj* l_int_neg___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_5; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
x_5 = l_int_neg__of__nat___main(x_3);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; 
x_6 = lean::nat_abs(x_0);
lean::dec(x_0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_6, x_8);
lean::dec(x_6);
x_11 = lean::nat_add(x_9, x_8);
lean::dec(x_8);
lean::dec(x_9);
x_14 = lean::nat2int(x_11);
lean::dec(x_11);
return x_14;
}
}
}
obj* l_int_add___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::int_dec_lt(x_1, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_add(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = lean::nat2int(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; 
x_14 = lean::nat_abs(x_1);
lean::dec(x_1);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_14, x_16);
lean::dec(x_14);
x_19 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_22 = l_int_sub__nat__nat(x_4, x_19);
return x_22;
}
}
else
{
obj* x_23; obj* x_25; obj* x_26; uint8 x_28; 
x_23 = lean::nat_abs(x_0);
lean::dec(x_0);
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_sub(x_23, x_25);
lean::dec(x_23);
x_28 = lean::int_dec_lt(x_1, x_2);
if (x_28 == 0)
{
obj* x_29; obj* x_31; obj* x_34; 
x_29 = lean::nat_abs(x_1);
lean::dec(x_1);
x_31 = lean::nat_add(x_26, x_25);
lean::dec(x_25);
lean::dec(x_26);
x_34 = l_int_sub__nat__nat(x_29, x_31);
return x_34;
}
else
{
obj* x_35; obj* x_37; obj* x_39; obj* x_42; obj* x_45; 
x_35 = lean::nat_abs(x_1);
lean::dec(x_1);
x_37 = lean::nat_sub(x_35, x_25);
lean::dec(x_35);
x_39 = lean::nat_add(x_26, x_37);
lean::dec(x_37);
lean::dec(x_26);
x_42 = lean::nat_add(x_39, x_25);
lean::dec(x_25);
lean::dec(x_39);
x_45 = lean::int_neg_succ_of_nat(x_42);
lean::dec(x_42);
return x_45;
}
}
}
}
obj* l_int_mul___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::int_dec_lt(x_1, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_mul(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = lean::nat2int(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; 
x_14 = lean::nat_abs(x_1);
lean::dec(x_1);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_14, x_16);
lean::dec(x_14);
x_19 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_22 = lean::nat_mul(x_4, x_19);
lean::dec(x_19);
lean::dec(x_4);
x_25 = l_int_neg__of__nat___main(x_22);
return x_25;
}
}
else
{
obj* x_26; obj* x_28; obj* x_29; uint8 x_31; 
x_26 = lean::nat_abs(x_0);
lean::dec(x_0);
x_28 = lean::mk_nat_obj(1u);
x_29 = lean::nat_sub(x_26, x_28);
lean::dec(x_26);
x_31 = lean::int_dec_lt(x_1, x_2);
if (x_31 == 0)
{
obj* x_32; obj* x_34; obj* x_37; obj* x_40; 
x_32 = lean::nat_abs(x_1);
lean::dec(x_1);
x_34 = lean::nat_add(x_29, x_28);
lean::dec(x_28);
lean::dec(x_29);
x_37 = lean::nat_mul(x_34, x_32);
lean::dec(x_32);
lean::dec(x_34);
x_40 = l_int_neg__of__nat___main(x_37);
return x_40;
}
else
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_53; 
x_41 = lean::nat_abs(x_1);
lean::dec(x_1);
x_43 = lean::nat_sub(x_41, x_28);
lean::dec(x_41);
x_45 = lean::nat_add(x_29, x_28);
lean::dec(x_29);
x_47 = lean::nat_add(x_43, x_28);
lean::dec(x_28);
lean::dec(x_43);
x_50 = lean::nat_mul(x_45, x_47);
lean::dec(x_47);
lean::dec(x_45);
x_53 = lean::nat2int(x_50);
lean::dec(x_50);
return x_53;
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
obj* x_1; uint8 x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_5; uint8 x_6; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
lean::dec(x_5);
lean::dec(x_3);
if (x_6 == 0)
{
obj* x_9; 
x_9 = l_int_one;
lean::inc(x_9);
return x_9;
}
else
{
obj* x_11; 
x_11 = l_int_zero;
lean::inc(x_11);
return x_11;
}
}
else
{
obj* x_14; 
lean::dec(x_0);
x_14 = l_int_sign___main___closed__1;
lean::inc(x_14);
return x_14;
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
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::int_dec_lt(x_1, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_div(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = lean::nat2int(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_27; 
x_14 = lean::nat_abs(x_1);
lean::dec(x_1);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_14, x_16);
lean::dec(x_14);
x_19 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_22 = lean::nat_div(x_4, x_19);
lean::dec(x_19);
lean::dec(x_4);
x_25 = lean::nat2int(x_22);
lean::dec(x_22);
x_27 = lean::int_neg(x_25);
lean::dec(x_25);
return x_27;
}
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; 
x_29 = lean::nat_abs(x_0);
lean::dec(x_0);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_sub(x_29, x_31);
lean::dec(x_29);
x_34 = lean::int_dec_lt(x_1, x_2);
if (x_34 == 0)
{
obj* x_36; obj* x_38; uint8 x_39; 
lean::dec(x_31);
x_36 = lean::nat_abs(x_1);
lean::dec(x_1);
x_38 = lean::mk_nat_obj(0u);
x_39 = lean::nat_dec_eq(x_36, x_38);
lean::dec(x_38);
if (x_39 == 0)
{
obj* x_41; obj* x_44; 
x_41 = lean::nat_div(x_32, x_36);
lean::dec(x_36);
lean::dec(x_32);
x_44 = lean::int_neg_succ_of_nat(x_41);
lean::dec(x_41);
return x_44;
}
else
{
obj* x_48; 
lean::dec(x_32);
lean::dec(x_36);
x_48 = l_int_zero;
lean::inc(x_48);
return x_48;
}
}
else
{
obj* x_50; obj* x_52; obj* x_54; obj* x_56; obj* x_59; obj* x_62; 
x_50 = lean::nat_abs(x_1);
lean::dec(x_1);
x_52 = lean::nat_sub(x_50, x_31);
lean::dec(x_50);
x_54 = lean::nat_add(x_52, x_31);
lean::dec(x_52);
x_56 = lean::nat_div(x_32, x_54);
lean::dec(x_54);
lean::dec(x_32);
x_59 = lean::nat_add(x_56, x_31);
lean::dec(x_31);
lean::dec(x_56);
x_62 = lean::nat2int(x_59);
lean::dec(x_59);
return x_62;
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
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::nat_abs(x_1);
lean::dec(x_1);
x_8 = lean::nat_mod(x_4, x_6);
lean::dec(x_6);
lean::dec(x_4);
x_11 = lean::nat2int(x_8);
lean::dec(x_8);
return x_11;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_25; 
x_13 = lean::nat_abs(x_0);
lean::dec(x_0);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_13, x_15);
lean::dec(x_13);
x_18 = lean::nat_abs(x_1);
lean::dec(x_1);
x_20 = lean::nat_mod(x_16, x_18);
lean::dec(x_16);
x_22 = lean::nat_add(x_20, x_15);
lean::dec(x_15);
lean::dec(x_20);
x_25 = l_int_sub__nat__nat(x_18, x_22);
return x_25;
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
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_6; uint8 x_7; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
uint8 x_9; 
x_9 = lean::int_dec_lt(x_1, x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_15; 
x_10 = lean::nat_abs(x_1);
lean::dec(x_1);
x_12 = lean::nat_div(x_4, x_10);
lean::dec(x_10);
lean::dec(x_4);
x_15 = lean::nat2int(x_12);
lean::dec(x_12);
return x_15;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_27; obj* x_30; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_4, x_17);
lean::dec(x_4);
x_20 = lean::nat_abs(x_1);
lean::dec(x_1);
x_22 = lean::nat_sub(x_20, x_17);
lean::dec(x_20);
x_24 = lean::nat_add(x_22, x_17);
lean::dec(x_17);
lean::dec(x_22);
x_27 = lean::nat_div(x_18, x_24);
lean::dec(x_24);
lean::dec(x_18);
x_30 = lean::int_neg_succ_of_nat(x_27);
lean::dec(x_27);
return x_30;
}
}
else
{
obj* x_34; 
lean::dec(x_4);
lean::dec(x_1);
x_34 = l_int_zero;
lean::inc(x_34);
return x_34;
}
}
else
{
obj* x_36; obj* x_38; obj* x_39; uint8 x_41; 
x_36 = lean::nat_abs(x_0);
lean::dec(x_0);
x_38 = lean::mk_nat_obj(1u);
x_39 = lean::nat_sub(x_36, x_38);
lean::dec(x_36);
x_41 = lean::int_dec_lt(x_1, x_2);
if (x_41 == 0)
{
obj* x_43; obj* x_45; uint8 x_46; 
lean::dec(x_38);
x_43 = lean::nat_abs(x_1);
lean::dec(x_1);
x_45 = lean::mk_nat_obj(0u);
x_46 = lean::nat_dec_eq(x_43, x_45);
lean::dec(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_51; 
x_48 = lean::nat_div(x_39, x_43);
lean::dec(x_43);
lean::dec(x_39);
x_51 = lean::int_neg_succ_of_nat(x_48);
lean::dec(x_48);
return x_51;
}
else
{
obj* x_55; 
lean::dec(x_39);
lean::dec(x_43);
x_55 = l_int_zero;
lean::inc(x_55);
return x_55;
}
}
else
{
obj* x_57; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_69; 
x_57 = lean::nat_abs(x_1);
lean::dec(x_1);
x_59 = lean::nat_sub(x_57, x_38);
lean::dec(x_57);
x_61 = lean::nat_add(x_39, x_38);
lean::dec(x_39);
x_63 = lean::nat_add(x_59, x_38);
lean::dec(x_38);
lean::dec(x_59);
x_66 = lean::nat_div(x_61, x_63);
lean::dec(x_63);
lean::dec(x_61);
x_69 = lean::nat2int(x_66);
lean::dec(x_66);
return x_69;
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
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_6; uint8 x_7; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
uint8 x_9; 
x_9 = lean::int_dec_lt(x_1, x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_15; 
x_10 = lean::nat_abs(x_1);
lean::dec(x_1);
x_12 = lean::nat_mod(x_4, x_10);
lean::dec(x_10);
lean::dec(x_4);
x_15 = lean::nat2int(x_12);
lean::dec(x_12);
return x_15;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_29; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_4, x_17);
lean::dec(x_4);
x_20 = lean::nat_abs(x_1);
lean::dec(x_1);
x_22 = lean::nat_sub(x_20, x_17);
lean::dec(x_20);
x_24 = lean::nat_add(x_22, x_17);
lean::dec(x_17);
x_26 = lean::nat_mod(x_18, x_24);
lean::dec(x_24);
lean::dec(x_18);
x_29 = l_int_sub__nat__nat(x_26, x_22);
return x_29;
}
}
else
{
obj* x_32; 
lean::dec(x_4);
lean::dec(x_1);
x_32 = l_int_zero;
lean::inc(x_32);
return x_32;
}
}
else
{
obj* x_34; obj* x_36; obj* x_37; uint8 x_39; 
x_34 = lean::nat_abs(x_0);
lean::dec(x_0);
x_36 = lean::mk_nat_obj(1u);
x_37 = lean::nat_sub(x_34, x_36);
lean::dec(x_34);
x_39 = lean::int_dec_lt(x_1, x_2);
if (x_39 == 0)
{
obj* x_40; obj* x_42; obj* x_44; obj* x_47; 
x_40 = lean::nat_abs(x_1);
lean::dec(x_1);
x_42 = lean::nat_mod(x_37, x_40);
lean::dec(x_37);
x_44 = lean::nat_add(x_42, x_36);
lean::dec(x_36);
lean::dec(x_42);
x_47 = l_int_sub__nat__nat(x_40, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_60; obj* x_62; 
x_48 = lean::nat_abs(x_1);
lean::dec(x_1);
x_50 = lean::nat_sub(x_48, x_36);
lean::dec(x_48);
x_52 = lean::nat_add(x_37, x_36);
lean::dec(x_37);
x_54 = lean::nat_add(x_50, x_36);
lean::dec(x_36);
lean::dec(x_50);
x_57 = lean::nat_mod(x_52, x_54);
lean::dec(x_54);
lean::dec(x_52);
x_60 = lean::nat2int(x_57);
lean::dec(x_57);
x_62 = lean::int_neg(x_60);
lean::dec(x_60);
return x_62;
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
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::int_dec_lt(x_1, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_div(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = lean::nat2int(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_27; 
x_14 = lean::nat_abs(x_1);
lean::dec(x_1);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_14, x_16);
lean::dec(x_14);
x_19 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_22 = lean::nat_div(x_4, x_19);
lean::dec(x_19);
lean::dec(x_4);
x_25 = lean::nat2int(x_22);
lean::dec(x_22);
x_27 = lean::int_neg(x_25);
lean::dec(x_25);
return x_27;
}
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; 
x_29 = lean::nat_abs(x_0);
lean::dec(x_0);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_sub(x_29, x_31);
lean::dec(x_29);
x_34 = lean::int_dec_lt(x_1, x_2);
if (x_34 == 0)
{
obj* x_35; obj* x_37; obj* x_40; obj* x_43; obj* x_45; 
x_35 = lean::nat_abs(x_1);
lean::dec(x_1);
x_37 = lean::nat_add(x_32, x_31);
lean::dec(x_31);
lean::dec(x_32);
x_40 = lean::nat_div(x_37, x_35);
lean::dec(x_35);
lean::dec(x_37);
x_43 = lean::nat2int(x_40);
lean::dec(x_40);
x_45 = lean::int_neg(x_43);
lean::dec(x_43);
return x_45;
}
else
{
obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_59; 
x_47 = lean::nat_abs(x_1);
lean::dec(x_1);
x_49 = lean::nat_sub(x_47, x_31);
lean::dec(x_47);
x_51 = lean::nat_add(x_32, x_31);
lean::dec(x_32);
x_53 = lean::nat_add(x_49, x_31);
lean::dec(x_31);
lean::dec(x_49);
x_56 = lean::nat_div(x_51, x_53);
lean::dec(x_53);
lean::dec(x_51);
x_59 = lean::nat2int(x_56);
lean::dec(x_56);
return x_59;
}
}
}
}
obj* l_int_rem___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_int_nat__abs___main___closed__1;
x_3 = lean::int_dec_lt(x_0, x_2);
if (x_3 == 0)
{
obj* x_4; uint8 x_6; 
x_4 = lean::nat_abs(x_0);
lean::dec(x_0);
x_6 = lean::int_dec_lt(x_1, x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::nat_abs(x_1);
lean::dec(x_1);
x_9 = lean::nat_mod(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = lean::nat2int(x_9);
lean::dec(x_9);
return x_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_25; 
x_14 = lean::nat_abs(x_1);
lean::dec(x_1);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_sub(x_14, x_16);
lean::dec(x_14);
x_19 = lean::nat_add(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_22 = lean::nat_mod(x_4, x_19);
lean::dec(x_19);
lean::dec(x_4);
x_25 = lean::nat2int(x_22);
lean::dec(x_22);
return x_25;
}
}
else
{
obj* x_27; obj* x_29; obj* x_30; uint8 x_32; 
x_27 = lean::nat_abs(x_0);
lean::dec(x_0);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_sub(x_27, x_29);
lean::dec(x_27);
x_32 = lean::int_dec_lt(x_1, x_2);
if (x_32 == 0)
{
obj* x_33; obj* x_35; obj* x_38; obj* x_41; obj* x_43; 
x_33 = lean::nat_abs(x_1);
lean::dec(x_1);
x_35 = lean::nat_add(x_30, x_29);
lean::dec(x_29);
lean::dec(x_30);
x_38 = lean::nat_mod(x_35, x_33);
lean::dec(x_33);
lean::dec(x_35);
x_41 = lean::nat2int(x_38);
lean::dec(x_38);
x_43 = lean::int_neg(x_41);
lean::dec(x_41);
return x_43;
}
else
{
obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_57; obj* x_59; 
x_45 = lean::nat_abs(x_1);
lean::dec(x_1);
x_47 = lean::nat_sub(x_45, x_29);
lean::dec(x_45);
x_49 = lean::nat_add(x_30, x_29);
lean::dec(x_30);
x_51 = lean::nat_add(x_47, x_29);
lean::dec(x_29);
lean::dec(x_47);
x_54 = lean::nat_mod(x_49, x_51);
lean::dec(x_51);
lean::dec(x_49);
x_57 = lean::nat2int(x_54);
lean::dec(x_54);
x_59 = lean::int_neg(x_57);
lean::dec(x_57);
return x_59;
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
obj* x_1; uint8 x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
return x_3;
}
else
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
return x_6;
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
uint8 l___private_3285259795__dec__nonneg___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_nat__abs___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
lean::dec(x_0);
if (x_2 == 0)
{
uint8 x_4; 
x_4 = l_true_decidable;
return x_4;
}
else
{
uint8 x_5; 
x_5 = l_false_decidable;
return x_5;
}
}
}
obj* l___private_3285259795__dec__nonneg___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l___private_3285259795__dec__nonneg___main(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
uint8 l___private_3285259795__dec__nonneg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l___private_3285259795__dec__nonneg___main(x_0);
return x_1;
}
}
obj* l___private_3285259795__dec__nonneg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l___private_3285259795__dec__nonneg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_int_dec__le___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_le(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_int_dec__lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_lt(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
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

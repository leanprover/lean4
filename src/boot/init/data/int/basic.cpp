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
obj* l_int_neg__of__nat(obj*);
obj* l_int_has__sub;
obj* l___private_3654102799__nonneg;
obj* l_int_add___boxed(obj*, obj*);
obj* l_int_neg___boxed(obj*);
obj* l_int_repr___main(obj*);
obj* l_int_div___boxed(obj*, obj*);
obj* l_int_to__nat___main(obj*);
obj* l___private_1909995369__dec__nonneg___boxed(obj*);
obj* l_int_sub___boxed(obj*, obj*);
obj* l_int_has__mul;
obj* l_int_lt;
obj* l_int_neg__of__nat___main(obj*);
obj* l_int_has__lt;
obj* l_int_int_decidable__eq;
obj* l___private_3654102799__nonneg___main;
obj* l_int_nat__abs___boxed(obj*);
obj* l_int_sub__nat__nat(obj*, obj*);
obj* l_int_dec__lt___boxed(obj*, obj*);
obj* l_int_zero;
obj* l_int_has__div;
obj* l_int_div___main(obj*, obj*);
obj* l_int_has__mod;
obj* l_int_sign(obj*);
obj* l_int_repr___main___closed__1;
obj* l_int_to__nat(obj*);
obj* l_int_dec__eq___boxed(obj*, obj*);
obj* l_int_has__coe(obj*);
obj* l_int_has__le;
obj* l_int_has__one;
obj* l_int_nat__mod(obj*, obj*);
obj* l_int_mod___boxed(obj*, obj*);
obj* l_int_has__neg;
obj* l_int_repr___main___closed__2;
obj* l_int_has__to__string;
obj* l_int_mod___main(obj*, obj*);
obj* l_int_mul___boxed(obj*, obj*);
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
return x_1;
}
}
obj* _init_l_int_zero() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_int_one() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(1u);
x_1 = lean::nat2int(x_0);
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
obj* _init_l___private_3654102799__nonneg___main() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l___private_3654102799__nonneg() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
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
return x_8;
}
else
{
obj* x_10; 
lean::dec(x_0);
x_10 = l_int_zero;
lean::inc(x_10);
return x_10;
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
obj* l_int_neg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::int_neg(x_0);
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
return x_12;
}
else
{
obj* x_14; obj* x_17; 
lean::dec(x_2);
x_14 = lean::nat_sub(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
x_17 = lean::nat2int(x_14);
return x_17;
}
}
}
obj* l_int_add___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_add(x_0, x_1);
return x_2;
}
}
obj* l_int_mul___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_mul(x_0, x_1);
return x_2;
}
}
obj* _init_l_int_has__neg() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_neg___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_int_has__add() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_add___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__mul() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_mul___boxed), 2, 0);
return x_0;
}
}
obj* l_int_sub___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_sub(x_0, x_1);
return x_2;
}
}
obj* _init_l_int_has__sub() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_sub___boxed), 2, 0);
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
obj* l_int_dec__eq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::int_dec_eq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_int_int_decidable__eq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_dec__eq___boxed), 2, 0);
return x_0;
}
}
obj* l___private_1909995369__dec__nonneg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::int_dec_nonneg(x_0);
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
obj* l_int_nat__abs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::nat_abs(x_0);
return x_1;
}
}
obj* _init_l_int_repr___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_int_repr___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* l_int_repr___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_repr___main___closed__1;
x_2 = lean::int_dec_lt(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_5; 
x_3 = lean::nat_abs(x_0);
lean::dec(x_0);
x_5 = lean::nat2int(x_3);
x_0 = x_5;
goto _start;
}
else
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_19; 
x_7 = lean::nat_abs(x_0);
lean::dec(x_0);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_7, x_9);
lean::dec(x_7);
x_12 = lean::nat_add(x_10, x_9);
lean::dec(x_9);
lean::dec(x_10);
x_15 = lean::nat2int(x_12);
x_16 = l_int_repr___main(x_15);
x_17 = l_int_repr___main___closed__2;
lean::inc(x_17);
x_19 = lean::string_append(x_17, x_16);
lean::dec(x_16);
return x_19;
}
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
obj* _init_l_int_sign___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_int_one;
x_1 = lean::int_neg(x_0);
return x_1;
}
}
obj* l_int_sign___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_repr___main___closed__1;
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
x_2 = l_int_repr___main___closed__1;
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
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_24; obj* x_25; 
x_13 = lean::nat_abs(x_1);
lean::dec(x_1);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_13, x_15);
lean::dec(x_13);
x_18 = lean::nat_add(x_16, x_15);
lean::dec(x_15);
lean::dec(x_16);
x_21 = lean::nat_div(x_4, x_18);
lean::dec(x_18);
lean::dec(x_4);
x_24 = lean::nat2int(x_21);
x_25 = lean::int_neg(x_24);
lean::dec(x_24);
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
obj* x_33; obj* x_35; obj* x_38; obj* x_41; obj* x_42; 
x_33 = lean::nat_abs(x_1);
lean::dec(x_1);
x_35 = lean::nat_add(x_30, x_29);
lean::dec(x_29);
lean::dec(x_30);
x_38 = lean::nat_div(x_35, x_33);
lean::dec(x_33);
lean::dec(x_35);
x_41 = lean::nat2int(x_38);
x_42 = lean::int_neg(x_41);
lean::dec(x_41);
return x_42;
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_56; 
x_44 = lean::nat_abs(x_1);
lean::dec(x_1);
x_46 = lean::nat_sub(x_44, x_29);
lean::dec(x_44);
x_48 = lean::nat_add(x_30, x_29);
lean::dec(x_30);
x_50 = lean::nat_add(x_46, x_29);
lean::dec(x_29);
lean::dec(x_46);
x_53 = lean::nat_div(x_48, x_50);
lean::dec(x_50);
lean::dec(x_48);
x_56 = lean::nat2int(x_53);
return x_56;
}
}
}
}
obj* l_int_div___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_div(x_0, x_1);
return x_2;
}
}
obj* l_int_mod___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_int_repr___main___closed__1;
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
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_24; 
x_13 = lean::nat_abs(x_1);
lean::dec(x_1);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_13, x_15);
lean::dec(x_13);
x_18 = lean::nat_add(x_16, x_15);
lean::dec(x_15);
lean::dec(x_16);
x_21 = lean::nat_mod(x_4, x_18);
lean::dec(x_18);
lean::dec(x_4);
x_24 = lean::nat2int(x_21);
return x_24;
}
}
else
{
obj* x_25; obj* x_27; obj* x_28; uint8 x_30; 
x_25 = lean::nat_abs(x_0);
lean::dec(x_0);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_25, x_27);
lean::dec(x_25);
x_30 = lean::int_dec_lt(x_1, x_2);
if (x_30 == 0)
{
obj* x_31; obj* x_33; obj* x_36; obj* x_39; obj* x_40; 
x_31 = lean::nat_abs(x_1);
lean::dec(x_1);
x_33 = lean::nat_add(x_28, x_27);
lean::dec(x_27);
lean::dec(x_28);
x_36 = lean::nat_mod(x_33, x_31);
lean::dec(x_31);
lean::dec(x_33);
x_39 = lean::nat2int(x_36);
x_40 = lean::int_neg(x_39);
lean::dec(x_39);
return x_40;
}
else
{
obj* x_42; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_54; obj* x_55; 
x_42 = lean::nat_abs(x_1);
lean::dec(x_1);
x_44 = lean::nat_sub(x_42, x_27);
lean::dec(x_42);
x_46 = lean::nat_add(x_28, x_27);
lean::dec(x_28);
x_48 = lean::nat_add(x_44, x_27);
lean::dec(x_27);
lean::dec(x_44);
x_51 = lean::nat_mod(x_46, x_48);
lean::dec(x_48);
lean::dec(x_46);
x_54 = lean::nat2int(x_51);
x_55 = lean::int_neg(x_54);
lean::dec(x_54);
return x_55;
}
}
}
}
obj* l_int_mod___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::int_mod(x_0, x_1);
return x_2;
}
}
obj* _init_l_int_has__div() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_div___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_int_has__mod() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_int_mod___boxed), 2, 0);
return x_0;
}
}
obj* l_int_to__nat___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_int_repr___main___closed__1;
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
obj* x_2; obj* x_5; 
x_2 = lean::int_mod(x_0, x_1);
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_int_to__nat___main(x_2);
return x_5;
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
 l_int_zero = _init_l_int_zero();
 l_int_one = _init_l_int_one();
 l_int_has__zero = _init_l_int_has__zero();
 l_int_has__one = _init_l_int_has__one();
 l___private_3654102799__nonneg___main = _init_l___private_3654102799__nonneg___main();
 l___private_3654102799__nonneg = _init_l___private_3654102799__nonneg();
 l_int_has__neg = _init_l_int_has__neg();
 l_int_has__add = _init_l_int_has__add();
 l_int_has__mul = _init_l_int_has__mul();
 l_int_has__sub = _init_l_int_has__sub();
 l_int_le = _init_l_int_le();
 l_int_has__le = _init_l_int_has__le();
 l_int_lt = _init_l_int_lt();
 l_int_has__lt = _init_l_int_has__lt();
 l_int_int_decidable__eq = _init_l_int_int_decidable__eq();
 l_int_repr___main___closed__1 = _init_l_int_repr___main___closed__1();
 l_int_repr___main___closed__2 = _init_l_int_repr___main___closed__2();
 l_int_has__repr = _init_l_int_has__repr();
 l_int_has__to__string = _init_l_int_has__to__string();
 l_int_sign___main___closed__1 = _init_l_int_sign___main___closed__1();
 l_int_has__div = _init_l_int_has__div();
 l_int_has__mod = _init_l_int_has__mod();
}

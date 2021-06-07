// Lean compiler output
// Module: Init.Data.Int.Basic
// Imports: Init.Coe Init.Data.Nat.Div Init.Data.List.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Int_instNegInt___closed__1;
static lean_object* l_Int_instAddInt___closed__1;
lean_object* l_Int_toNat_match__1(lean_object*);
lean_object* l_Int_instNegInt;
lean_object* l_Int_natMod(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
uint8_t l_Int_instDecidableEqInt(lean_object*, lean_object*);
lean_object* l_Int_negSucc___boxed(lean_object*);
static lean_object* l_Int_instMulInt___closed__1;
lean_object* l_Int_decLt___boxed(lean_object*, lean_object*);
lean_object* l_Int_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Int_instSubInt;
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_instDivInt;
lean_object* l_Int_decLe___boxed(lean_object*, lean_object*);
static lean_object* l_Int_instDivInt___closed__1;
lean_object* l_Int_div___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Int_Basic_0__Int_decNonneg___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_negOfNat_match__1(lean_object*);
lean_object* l_Int_instDecidableEqInt___boxed(lean_object*, lean_object*);
static lean_object* l_Int_instSubInt___closed__1;
lean_object* l_Int_negOfNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_div_match__1(lean_object*);
lean_object* l_Int_instHPowIntNatInt;
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
lean_object* l_Int_instModInt;
lean_object* l_Int_toNat___boxed(lean_object*);
lean_object* l_Int_mod___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* l_Int_div_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_instLTInt;
lean_object* l_Int_instInhabitedInt;
static lean_object* l_Int_instModInt___closed__1;
lean_object* l_Int_negOfNat___boxed(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Int_negOfNat_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_instLEInt;
lean_object* l_Int_natMod___boxed(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Int_toNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_instCoeNatInt(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_toNat_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* l_Int_instOfNatInt(lean_object*);
lean_object* l_Int_div_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_subNatNat___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l_Int_instInhabitedInt___closed__1;
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_natAbs___boxed(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
static lean_object* l_Int_instHPowIntNatInt___closed__1;
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Int_instMulInt;
lean_object* l_Int_instAddInt;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Int_pow___closed__1;
lean_object* l_Int_pow___boxed(lean_object*, lean_object*);
lean_object* l_Int_ofNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Int_negSucc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_int_neg_succ_of_nat(x_1);
return x_2;
}
}
lean_object* l_instCoeNatInt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instInhabitedInt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_instInhabitedInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instInhabitedInt___closed__1;
return x_1;
}
}
lean_object* l_Int_negOfNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Int_negOfNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_negOfNat_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_negOfNat_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_negOfNat_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Int_negOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_int_neg_succ_of_nat(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Int_instInhabitedInt___closed__1;
return x_7;
}
}
}
lean_object* l_Int_negOfNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_negOfNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_neg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_int_neg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_subNatNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_nat_sub(x_2, x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_int_neg_succ_of_nat(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_nat_sub(x_1, x_2);
x_10 = lean_nat_to_int(x_9);
return x_10;
}
}
}
lean_object* l_Int_subNatNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_subNatNat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instNegInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_neg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instNegInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instNegInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instAddInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instAddInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instAddInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instMulInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instMulInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instMulInt___closed__1;
return x_1;
}
}
lean_object* l_Int_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_sub(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instSubInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instSubInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instSubInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instLEInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Int_instLTInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Int_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_eq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Int_instDecidableEqInt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Int_instDecidableEqInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_instDecidableEqInt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Data_Int_Basic_0__Int_decNonneg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_int_dec_nonneg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Int_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_le(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Int_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_int_dec_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Int_natAbs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_abs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_instOfNatInt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Int_div_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Int_instInhabitedInt___closed__1;
x_8 = lean_int_dec_lt(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_nat_abs(x_1);
x_10 = lean_int_dec_lt(x_2, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_nat_abs(x_2);
x_12 = lean_apply_2(x_3, x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_13 = lean_nat_abs(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_apply_2(x_4, x_9, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_nat_abs(x_1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_int_dec_lt(x_2, x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_nat_abs(x_2);
x_22 = lean_apply_2(x_5, x_19, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
x_23 = lean_nat_abs(x_2);
x_24 = lean_nat_sub(x_23, x_18);
lean_dec(x_23);
x_25 = lean_apply_2(x_6, x_19, x_24);
return x_25;
}
}
}
}
lean_object* l_Int_div_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_div_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Int_div_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Int_div_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Int_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_div(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Int_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_mod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instDivInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instDivInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instDivInt___closed__1;
return x_1;
}
}
static lean_object* _init_l_Int_instModInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instModInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instModInt___closed__1;
return x_1;
}
}
lean_object* l_Int_toNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Int_instInhabitedInt___closed__1;
x_5 = lean_int_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_nat_abs(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_nat_abs(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
lean_object* l_Int_toNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Int_toNat_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Int_toNat_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_toNat_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Int_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_instInhabitedInt___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_nat_abs(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(0u);
return x_5;
}
}
}
lean_object* l_Int_toNat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_toNat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Int_natMod(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_int_mod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Int_natMod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_natMod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_pow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* l_Int_pow(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Int_pow(x_1, x_6);
lean_dec(x_6);
x_8 = lean_int_mul(x_7, x_1);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Int_pow___closed__1;
return x_9;
}
}
}
lean_object* l_Int_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_pow(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_instHPowIntNatInt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_pow___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_instHPowIntNatInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_instHPowIntNatInt___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Coe(lean_object*);
lean_object* initialize_Init_Data_Nat_Div(lean_object*);
lean_object* initialize_Init_Data_List_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Int_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instInhabitedInt___closed__1 = _init_l_Int_instInhabitedInt___closed__1();
lean_mark_persistent(l_Int_instInhabitedInt___closed__1);
l_Int_instInhabitedInt = _init_l_Int_instInhabitedInt();
lean_mark_persistent(l_Int_instInhabitedInt);
l_Int_instNegInt___closed__1 = _init_l_Int_instNegInt___closed__1();
lean_mark_persistent(l_Int_instNegInt___closed__1);
l_Int_instNegInt = _init_l_Int_instNegInt();
lean_mark_persistent(l_Int_instNegInt);
l_Int_instAddInt___closed__1 = _init_l_Int_instAddInt___closed__1();
lean_mark_persistent(l_Int_instAddInt___closed__1);
l_Int_instAddInt = _init_l_Int_instAddInt();
lean_mark_persistent(l_Int_instAddInt);
l_Int_instMulInt___closed__1 = _init_l_Int_instMulInt___closed__1();
lean_mark_persistent(l_Int_instMulInt___closed__1);
l_Int_instMulInt = _init_l_Int_instMulInt();
lean_mark_persistent(l_Int_instMulInt);
l_Int_instSubInt___closed__1 = _init_l_Int_instSubInt___closed__1();
lean_mark_persistent(l_Int_instSubInt___closed__1);
l_Int_instSubInt = _init_l_Int_instSubInt();
lean_mark_persistent(l_Int_instSubInt);
l_Int_instLEInt = _init_l_Int_instLEInt();
lean_mark_persistent(l_Int_instLEInt);
l_Int_instLTInt = _init_l_Int_instLTInt();
lean_mark_persistent(l_Int_instLTInt);
l_Int_instDivInt___closed__1 = _init_l_Int_instDivInt___closed__1();
lean_mark_persistent(l_Int_instDivInt___closed__1);
l_Int_instDivInt = _init_l_Int_instDivInt();
lean_mark_persistent(l_Int_instDivInt);
l_Int_instModInt___closed__1 = _init_l_Int_instModInt___closed__1();
lean_mark_persistent(l_Int_instModInt___closed__1);
l_Int_instModInt = _init_l_Int_instModInt();
lean_mark_persistent(l_Int_instModInt);
l_Int_pow___closed__1 = _init_l_Int_pow___closed__1();
lean_mark_persistent(l_Int_pow___closed__1);
l_Int_instHPowIntNatInt___closed__1 = _init_l_Int_instHPowIntNatInt___closed__1();
lean_mark_persistent(l_Int_instHPowIntNatInt___closed__1);
l_Int_instHPowIntNatInt = _init_l_Int_instHPowIntNatInt();
lean_mark_persistent(l_Int_instHPowIntNatInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

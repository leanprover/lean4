// Lean compiler output
// Module: Lean.Data.Rat
// Imports: Init.NotationExtra Init.Data.ToString.Macro Init.Data.Int.DivMod Init.Data.Nat.Gcd
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Rat_0__Lean_beqRat____x40_Lean_Data_Rat___hyg_36_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instLE;
LEAN_EXPORT lean_object* l_Lean_Rat_instOfNat(lean_object*);
static lean_object* l_Lean_instBEqRat___closed__1;
LEAN_EXPORT lean_object* l_Lean_instReprRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_neg(lean_object*);
static lean_object* l_Lean_instToStringRat___closed__2;
LEAN_EXPORT uint8_t l_Lean_instDecidableEqRat(lean_object*, lean_object*);
static lean_object* l_Lean_Rat_instSub___closed__1;
LEAN_EXPORT lean_object* l_Lean_Rat_instSub;
LEAN_EXPORT lean_object* l_Lean_mkRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableEqRat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instCoeInt(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Rat_instDecidableLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_normalize___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Rat_instDecidableLt(lean_object*, lean_object*);
static lean_object* l_Lean_Rat_instMul___closed__1;
LEAN_EXPORT lean_object* l_Lean_Rat_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedRat___closed__2;
static lean_object* l_Lean_instInhabitedRat___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Data_Rat_0__Lean_decEqRat____x40_Lean_Data_Rat___hyg_110_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Rat_0__Lean_beqRat____x40_Lean_Data_Rat___hyg_36____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instMul;
LEAN_EXPORT lean_object* l_Lean_Rat_instLT;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Rat_instNeg;
LEAN_EXPORT lean_object* l_Lean_Rat_instDecidableLt___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_den___default;
LEAN_EXPORT lean_object* l_Lean_Rat_inv(lean_object*);
static lean_object* l_Lean_Rat_instNeg___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedRat;
static lean_object* l_Lean_Rat_instAdd___closed__1;
static lean_object* l_Lean_instReprRat___closed__2;
static lean_object* l_Lean_instReprRat___closed__1;
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringRat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instDecidableLe___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instToStringRat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprRat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Rat_0__Lean_decEqRat____x40_Lean_Data_Rat___hyg_110____boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_isInt___boxed(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Rat_floor___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instAdd;
LEAN_EXPORT uint8_t l_Lean_Rat_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lean_instToStringRat___closed__3;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_floor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_ceil(lean_object*);
static lean_object* l_Lean_mkRat___closed__1;
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Rat_isInt(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_sub(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instDiv___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Rat_instDiv(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqRat;
static lean_object* _init_l_Lean_Rat_den___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedRat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedRat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedRat___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedRat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedRat___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Rat_0__Lean_beqRat____x40_Lean_Data_Rat___hyg_36_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Rat_0__Lean_beqRat____x40_Lean_Data_Rat___hyg_36____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Rat_0__Lean_beqRat____x40_Lean_Data_Rat___hyg_36_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqRat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Rat_0__Lean_beqRat____x40_Lean_Data_Rat___hyg_36____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqRat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqRat___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Rat_0__Lean_decEqRat____x40_Lean_Data_Rat___hyg_110_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_int_dec_eq(x_3, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Rat_0__Lean_decEqRat____x40_Lean_Data_Rat___hyg_110____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Data_Rat_0__Lean_decEqRat____x40_Lean_Data_Rat___hyg_110_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableEqRat(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lean_Data_Rat_0__Lean_decEqRat____x40_Lean_Data_Rat___hyg_110_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableEqRat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableEqRat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instToStringRat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringRat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringRat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringRat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_7 = l_Lean_instInhabitedRat___closed__1;
x_8 = lean_int_dec_lt(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_nat_abs(x_5);
lean_dec(x_5);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_9);
x_11 = l_Lean_instToStringRat___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_instToStringRat___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_6);
lean_dec(x_6);
x_16 = lean_string_append(x_15, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_nat_abs(x_5);
lean_dec(x_5);
x_18 = lean_nat_sub(x_17, x_3);
lean_dec(x_17);
x_19 = lean_nat_add(x_18, x_3);
lean_dec(x_18);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = l_Lean_instToStringRat___closed__3;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_instToStringRat___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_instToStringRat___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_string_append(x_26, x_6);
lean_dec(x_6);
x_28 = lean_string_append(x_27, x_23);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_instInhabitedRat___closed__1;
x_31 = lean_int_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_nat_abs(x_29);
lean_dec(x_29);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_nat_abs(x_29);
lean_dec(x_29);
x_35 = lean_nat_sub(x_34, x_3);
lean_dec(x_34);
x_36 = lean_nat_add(x_35, x_3);
lean_dec(x_35);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_36);
x_38 = l_Lean_instToStringRat___closed__3;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_instReprRat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprRat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : Rat)/", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_8 = l_Lean_instInhabitedRat___closed__1;
x_9 = lean_int_dec_lt(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_nat_abs(x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = l_Lean_instReprRat___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_instReprRat___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_7);
lean_dec(x_7);
x_17 = l_Lean_instToStringRat___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_nat_abs(x_6);
lean_dec(x_6);
x_21 = lean_nat_sub(x_20, x_4);
lean_dec(x_20);
x_22 = lean_nat_add(x_21, x_4);
lean_dec(x_21);
x_23 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_24 = l_Lean_instToStringRat___closed__3;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_instReprRat___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_instReprRat___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_string_append(x_29, x_7);
lean_dec(x_7);
x_31 = l_Lean_instToStringRat___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lean_instInhabitedRat___closed__1;
x_36 = lean_int_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Int_repr(x_34);
lean_dec(x_34);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Int_repr(x_34);
lean_dec(x_34);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Repr_addAppParen(x_40, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprRat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprRat(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_nat_abs(x_2);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_nat_gcd(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
x_8 = lean_nat_to_int(x_5);
x_9 = lean_int_div(x_2, x_8);
lean_dec(x_8);
x_10 = lean_nat_div(x_4, x_5);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_dec(x_5);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_normalize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Rat_normalize(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkRat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedRat___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_nat_abs(x_1);
x_7 = lean_nat_gcd(x_6, x_2);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_inc(x_7);
x_10 = lean_nat_to_int(x_7);
x_11 = lean_int_div(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_12 = lean_nat_div(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_mkRat___closed__1;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Rat_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Rat_isInt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Rat_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_26 = l_Lean_instInhabitedRat___closed__1;
x_27 = lean_int_dec_lt(x_3, x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_int_dec_eq(x_3, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_4 = x_29;
goto block_25;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_int_dec_lt(x_26, x_30);
lean_dec(x_30);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_int_dec_le(x_26, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_int_dec_eq(x_3, x_26);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
x_35 = lean_box(0);
x_4 = x_35;
goto block_25;
}
else
{
uint8_t x_36; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_int_dec_lt(x_26, x_32);
lean_dec(x_32);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = 1;
return x_37;
}
}
block_25:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_4);
x_5 = l_Lean_instInhabitedRat___closed__1;
x_6 = lean_int_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_int_mul(x_3, x_8);
lean_dec(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_mul(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_int_dec_lt(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_int_dec_le(x_15, x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_nat_to_int(x_17);
x_19 = lean_int_mul(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_mul(x_15, x_21);
lean_dec(x_21);
lean_dec(x_15);
x_23 = lean_int_dec_lt(x_19, x_22);
lean_dec(x_22);
lean_dec(x_19);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = 0;
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Rat_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_abs(x_4);
x_6 = lean_nat_gcd(x_3, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_nat_abs(x_7);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_nat_gcd(x_8, x_9);
lean_dec(x_8);
lean_inc(x_10);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_div(x_7, x_11);
lean_dec(x_11);
lean_inc(x_6);
x_13 = lean_nat_to_int(x_6);
x_14 = lean_int_div(x_4, x_13);
lean_dec(x_13);
x_15 = lean_int_mul(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = lean_nat_div(x_9, x_10);
lean_dec(x_10);
x_17 = lean_nat_div(x_3, x_6);
lean_dec(x_6);
x_18 = lean_nat_mul(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Rat_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_inv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_instInhabitedRat___closed__1;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_int_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_nat_abs(x_2);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_neg(x_11);
lean_dec(x_11);
x_13 = lean_nat_abs(x_2);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_div(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Rat_inv(x_2);
x_4 = l_Lean_Rat_mul(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Rat_div(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_nat_gcd(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_nat_div(x_3, x_5);
lean_dec(x_3);
x_9 = lean_nat_mul(x_8, x_4);
x_10 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_nat_to_int(x_8);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_int_mul(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_int_add(x_13, x_16);
lean_dec(x_16);
lean_dec(x_13);
x_18 = lean_nat_abs(x_17);
x_19 = lean_nat_gcd(x_18, x_5);
lean_dec(x_5);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_19, x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_19);
x_21 = lean_nat_to_int(x_19);
x_22 = lean_int_div(x_17, x_21);
lean_dec(x_21);
lean_dec(x_17);
x_23 = lean_nat_div(x_9, x_19);
lean_dec(x_19);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_4);
x_27 = lean_nat_to_int(x_4);
x_28 = lean_int_mul(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
lean_inc(x_3);
x_30 = lean_nat_to_int(x_3);
x_31 = lean_int_mul(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = lean_int_add(x_28, x_31);
lean_dec(x_31);
lean_dec(x_28);
x_33 = lean_nat_mul(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_sub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_nat_gcd(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_nat_div(x_3, x_5);
x_9 = lean_nat_mul(x_8, x_4);
lean_dec(x_8);
x_10 = lean_nat_to_int(x_4);
lean_inc(x_5);
x_11 = lean_nat_to_int(x_5);
x_12 = lean_int_ediv(x_10, x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_int_mul(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_nat_to_int(x_3);
x_16 = lean_int_ediv(x_15, x_11);
lean_dec(x_11);
lean_dec(x_15);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_int_sub(x_14, x_18);
lean_dec(x_18);
lean_dec(x_14);
x_20 = lean_nat_abs(x_19);
x_21 = lean_nat_gcd(x_20, x_5);
lean_dec(x_5);
lean_dec(x_20);
x_22 = lean_nat_dec_eq(x_21, x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_21);
x_23 = lean_nat_to_int(x_21);
x_24 = lean_int_div(x_19, x_23);
lean_dec(x_23);
lean_dec(x_19);
x_25 = lean_nat_div(x_9, x_21);
lean_dec(x_21);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
lean_inc(x_4);
x_29 = lean_nat_to_int(x_4);
x_30 = lean_int_mul(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_3);
x_32 = lean_nat_to_int(x_3);
x_33 = lean_int_mul(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = lean_int_sub(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
x_35 = lean_nat_mul(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_neg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_int_neg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_int_neg(x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Rat_floor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_floor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_nat_to_int(x_2);
x_7 = lean_int_mod(x_5, x_6);
lean_dec(x_6);
x_8 = l_Lean_instInhabitedRat___closed__1;
x_9 = lean_int_dec_lt(x_5, x_8);
lean_dec(x_5);
if (x_9 == 0)
{
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Rat_floor___closed__1;
x_11 = lean_int_sub(x_7, x_10);
lean_dec(x_7);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_ceil(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_nat_to_int(x_2);
x_7 = lean_int_mod(x_5, x_6);
lean_dec(x_6);
x_8 = l_Lean_instInhabitedRat___closed__1;
x_9 = lean_int_dec_lt(x_8, x_5);
lean_dec(x_5);
if (x_9 == 0)
{
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Rat_floor___closed__1;
x_11 = lean_int_add(x_7, x_10);
lean_dec(x_7);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Rat_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Rat_instDecidableLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Rat_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Rat_instDecidableLt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Rat_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Rat_instDecidableLe(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = l_Lean_Rat_lt(x_2, x_1);
x_4 = l_instDecidableNot___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_instDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Rat_instDecidableLe(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Rat_instAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Rat_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Rat_instAdd___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Rat_sub), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instSub() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Rat_instSub___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instNeg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Rat_neg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instNeg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Rat_instNeg___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Rat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Rat_instMul() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Rat_instMul___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_instDiv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Rat_inv(x_2);
x_4 = l_Lean_Rat_mul(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_instDiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Rat_instDiv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_instOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_nat_to_int(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Rat_instCoeInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Rat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Rat_den___default = _init_l_Lean_Rat_den___default();
lean_mark_persistent(l_Lean_Rat_den___default);
l_Lean_instInhabitedRat___closed__1 = _init_l_Lean_instInhabitedRat___closed__1();
lean_mark_persistent(l_Lean_instInhabitedRat___closed__1);
l_Lean_instInhabitedRat___closed__2 = _init_l_Lean_instInhabitedRat___closed__2();
lean_mark_persistent(l_Lean_instInhabitedRat___closed__2);
l_Lean_instInhabitedRat = _init_l_Lean_instInhabitedRat();
lean_mark_persistent(l_Lean_instInhabitedRat);
l_Lean_instBEqRat___closed__1 = _init_l_Lean_instBEqRat___closed__1();
lean_mark_persistent(l_Lean_instBEqRat___closed__1);
l_Lean_instBEqRat = _init_l_Lean_instBEqRat();
lean_mark_persistent(l_Lean_instBEqRat);
l_Lean_instToStringRat___closed__1 = _init_l_Lean_instToStringRat___closed__1();
lean_mark_persistent(l_Lean_instToStringRat___closed__1);
l_Lean_instToStringRat___closed__2 = _init_l_Lean_instToStringRat___closed__2();
lean_mark_persistent(l_Lean_instToStringRat___closed__2);
l_Lean_instToStringRat___closed__3 = _init_l_Lean_instToStringRat___closed__3();
lean_mark_persistent(l_Lean_instToStringRat___closed__3);
l_Lean_instReprRat___closed__1 = _init_l_Lean_instReprRat___closed__1();
lean_mark_persistent(l_Lean_instReprRat___closed__1);
l_Lean_instReprRat___closed__2 = _init_l_Lean_instReprRat___closed__2();
lean_mark_persistent(l_Lean_instReprRat___closed__2);
l_Lean_mkRat___closed__1 = _init_l_Lean_mkRat___closed__1();
lean_mark_persistent(l_Lean_mkRat___closed__1);
l_Lean_Rat_floor___closed__1 = _init_l_Lean_Rat_floor___closed__1();
lean_mark_persistent(l_Lean_Rat_floor___closed__1);
l_Lean_Rat_instLT = _init_l_Lean_Rat_instLT();
lean_mark_persistent(l_Lean_Rat_instLT);
l_Lean_Rat_instLE = _init_l_Lean_Rat_instLE();
lean_mark_persistent(l_Lean_Rat_instLE);
l_Lean_Rat_instAdd___closed__1 = _init_l_Lean_Rat_instAdd___closed__1();
lean_mark_persistent(l_Lean_Rat_instAdd___closed__1);
l_Lean_Rat_instAdd = _init_l_Lean_Rat_instAdd();
lean_mark_persistent(l_Lean_Rat_instAdd);
l_Lean_Rat_instSub___closed__1 = _init_l_Lean_Rat_instSub___closed__1();
lean_mark_persistent(l_Lean_Rat_instSub___closed__1);
l_Lean_Rat_instSub = _init_l_Lean_Rat_instSub();
lean_mark_persistent(l_Lean_Rat_instSub);
l_Lean_Rat_instNeg___closed__1 = _init_l_Lean_Rat_instNeg___closed__1();
lean_mark_persistent(l_Lean_Rat_instNeg___closed__1);
l_Lean_Rat_instNeg = _init_l_Lean_Rat_instNeg();
lean_mark_persistent(l_Lean_Rat_instNeg);
l_Lean_Rat_instMul___closed__1 = _init_l_Lean_Rat_instMul___closed__1();
lean_mark_persistent(l_Lean_Rat_instMul___closed__1);
l_Lean_Rat_instMul = _init_l_Lean_Rat_instMul();
lean_mark_persistent(l_Lean_Rat_instMul);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

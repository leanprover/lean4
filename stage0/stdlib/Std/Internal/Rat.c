// Lean compiler output
// Module: Std.Internal.Rat
// Imports: Init.NotationExtra Init.Data.ToString.Macro Init.Data.Int.DivMod.Basic Init.Data.Int.Linear Init.Data.Nat.Gcd
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
LEAN_EXPORT lean_object* l_Std_Internal_instBEqRat;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_add(lean_object*, lean_object*);
static lean_object* l_Std_Internal_instReprRat___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_mkRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instLE;
LEAN_EXPORT lean_object* l_Std_Internal_instReprRat;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instSub;
LEAN_EXPORT lean_object* l_Std_Internal_decEqRat____x40_Std_Internal_Rat___hyg_116____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instAdd;
static lean_object* l_Std_Internal_instInhabitedRat___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_instToStringRat;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instMul;
LEAN_EXPORT lean_object* l_Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_42____boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_instToStringRat___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instLT;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Std_Internal_instBEqRat___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_instToStringRat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDecidableLt___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Rat_instNeg___closed__0;
static lean_object* l_Std_Internal_instInhabitedRat___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_normalize(lean_object*);
static lean_object* l_Std_Internal_instToStringRat___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instCoeInt;
LEAN_EXPORT uint8_t l_Std_Internal_Rat_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_decEqRat____x40_Std_Internal_Rat___hyg_116_(lean_object*, lean_object*);
static lean_object* l_Std_Internal_Rat_instMul___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_mul(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
static lean_object* l_Std_Internal_Rat_instSub___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_div(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Rat_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instOfNat(lean_object*);
static lean_object* l_Std_Internal_mkRat___closed__0;
static lean_object* l_Std_Internal_Rat_instAdd___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_Rat_ceil(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_lt___boxed(lean_object*, lean_object*);
lean_object* l_Int_Linear_cdiv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Rat_instDecidableLe(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDiv___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instCoeInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprRat___lam__0(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDiv;
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Rat_isInt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_mul___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_instReprRat___lam__0___closed__1;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDiv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_inv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instNeg;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedRat;
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprRat___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instDecidableEqRat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_instDecidableEqRat(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Rat_floor(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_42_(lean_object*, lean_object*);
static lean_object* _init_l_Std_Internal_instInhabitedRat___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedRat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Internal_instInhabitedRat___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedRat() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_instInhabitedRat___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_42_(lean_object* x_1, lean_object* x_2) {
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
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_42____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_42_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_instBEqRat___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_beqRat____x40_Std_Internal_Rat___hyg_42____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_instBEqRat() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_instBEqRat___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_decEqRat____x40_Std_Internal_Rat___hyg_116_(lean_object* x_1, lean_object* x_2) {
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
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_decEqRat____x40_Std_Internal_Rat___hyg_116____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_decEqRat____x40_Std_Internal_Rat___hyg_116_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_instDecidableEqRat(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Internal_decEqRat____x40_Std_Internal_Rat___hyg_116_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instDecidableEqRat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_instDecidableEqRat(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_instToStringRat___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_instToStringRat___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instToStringRat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_10; uint8_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Std_Internal_instInhabitedRat___closed__0;
x_13 = lean_int_dec_lt(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_nat_abs(x_2);
lean_dec(x_2);
x_15 = l_Nat_reprFast(x_14);
x_4 = x_15;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_nat_abs(x_2);
lean_dec(x_2);
x_17 = lean_nat_sub(x_16, x_10);
lean_dec(x_16);
x_18 = l_Std_Internal_instToStringRat___lam__0___closed__1;
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_17, x_19);
lean_dec(x_17);
x_21 = l_Nat_reprFast(x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_4 = x_22;
goto block_9;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
x_23 = l_Std_Internal_instInhabitedRat___closed__0;
x_24 = lean_int_dec_lt(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_nat_abs(x_2);
lean_dec(x_2);
x_26 = l_Nat_reprFast(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_nat_abs(x_2);
lean_dec(x_2);
x_28 = lean_nat_sub(x_27, x_10);
lean_dec(x_27);
x_29 = l_Std_Internal_instToStringRat___lam__0___closed__1;
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_28);
x_32 = l_Nat_reprFast(x_31);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
return x_33;
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Std_Internal_instToStringRat___lam__0___closed__0;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Nat_reprFast(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Std_Internal_instToStringRat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_instToStringRat___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_instReprRat___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_instReprRat___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : Rat)/", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprRat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_16; uint8_t x_17; 
x_7 = l_Std_Internal_instReprRat___lam__0___closed__0;
x_16 = l_Std_Internal_instInhabitedRat___closed__0;
x_17 = lean_int_dec_lt(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_nat_abs(x_3);
lean_dec(x_3);
x_19 = l_Nat_reprFast(x_18);
x_8 = x_19;
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_nat_abs(x_3);
lean_dec(x_3);
x_21 = lean_nat_sub(x_20, x_5);
lean_dec(x_20);
x_22 = l_Std_Internal_instToStringRat___lam__0___closed__1;
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_21, x_23);
lean_dec(x_21);
x_25 = l_Nat_reprFast(x_24);
x_26 = lean_string_append(x_22, x_25);
lean_dec(x_25);
x_8 = x_26;
goto block_15;
}
block_15:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = l_Std_Internal_instReprRat___lam__0___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Nat_reprFast(x_4);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Std_Internal_instInhabitedRat___closed__0;
x_29 = lean_int_dec_lt(x_3, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Int_repr(x_3);
lean_dec(x_3);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Int_repr(x_3);
lean_dec(x_3);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Repr_addAppParen(x_33, x_27);
return x_34;
}
}
}
}
static lean_object* _init_l_Std_Internal_instReprRat() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_instReprRat___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprRat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_instReprRat___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_nat_abs(x_2);
x_5 = lean_nat_gcd(x_4, x_3);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
lean_inc(x_5);
x_11 = lean_nat_to_int(x_5);
x_12 = lean_int_div(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_13 = lean_nat_div(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
lean_inc(x_5);
x_14 = lean_nat_to_int(x_5);
x_15 = lean_int_div(x_2, x_14);
lean_dec(x_14);
lean_dec(x_2);
x_16 = lean_nat_div(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l_Std_Internal_mkRat___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Std_Internal_instInhabitedRat___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_mkRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_nat_abs(x_1);
x_6 = lean_nat_gcd(x_5, x_2);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
x_9 = lean_nat_to_int(x_6);
x_10 = lean_int_div(x_1, x_9);
lean_dec(x_9);
lean_dec(x_1);
x_11 = lean_nat_div(x_2, x_6);
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Std_Internal_mkRat___closed__0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Rat_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Rat_isInt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Rat_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_15 = l_Std_Internal_instInhabitedRat___closed__0;
x_24 = lean_int_dec_lt(x_3, x_15);
if (x_24 == 0)
{
x_16 = x_24;
goto block_23;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_int_dec_le(x_15, x_25);
lean_dec(x_25);
x_16 = x_26;
goto block_23;
}
block_14:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_int_mul(x_3, x_9);
lean_dec(x_9);
lean_dec(x_3);
x_11 = lean_nat_to_int(x_4);
x_12 = lean_int_mul(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_13 = lean_int_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
block_23:
{
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_int_dec_eq(x_3, x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_int_dec_lt(x_15, x_3);
if (x_18 == 0)
{
x_5 = x_17;
x_6 = x_18;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_int_dec_le(x_19, x_15);
lean_dec(x_19);
x_5 = x_17;
x_6 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_int_dec_lt(x_15, x_21);
lean_dec(x_21);
return x_22;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Rat_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_nat_abs(x_6);
x_9 = lean_nat_gcd(x_5, x_8);
lean_dec(x_8);
x_10 = lean_nat_abs(x_4);
x_11 = lean_nat_gcd(x_10, x_7);
lean_dec(x_10);
lean_inc(x_11);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_div(x_4, x_12);
lean_dec(x_12);
lean_inc(x_9);
x_14 = lean_nat_to_int(x_9);
x_15 = lean_int_div(x_6, x_14);
lean_dec(x_14);
lean_dec(x_6);
x_16 = lean_int_mul(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = lean_nat_div(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
x_18 = lean_nat_div(x_5, x_9);
lean_dec(x_9);
x_19 = lean_nat_mul(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_24 = lean_nat_abs(x_22);
x_25 = lean_nat_gcd(x_21, x_24);
lean_dec(x_24);
x_26 = lean_nat_abs(x_20);
x_27 = lean_nat_gcd(x_26, x_23);
lean_dec(x_26);
lean_inc(x_27);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_div(x_20, x_28);
lean_dec(x_28);
lean_inc(x_25);
x_30 = lean_nat_to_int(x_25);
x_31 = lean_int_div(x_22, x_30);
lean_dec(x_30);
lean_dec(x_22);
x_32 = lean_int_mul(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = lean_nat_div(x_23, x_27);
lean_dec(x_27);
lean_dec(x_23);
x_34 = lean_nat_div(x_21, x_25);
lean_dec(x_25);
x_35 = lean_nat_mul(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Rat_mul(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_inv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_Std_Internal_instInhabitedRat___closed__0;
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_int_dec_eq(x_2, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = lean_nat_to_int(x_3);
x_11 = lean_nat_abs(x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_nat_to_int(x_3);
x_13 = lean_nat_abs(x_2);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_nat_to_int(x_3);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = lean_nat_abs(x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = lean_nat_to_int(x_3);
x_22 = lean_int_neg(x_21);
lean_dec(x_21);
x_23 = lean_nat_abs(x_2);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_div(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Rat_inv(x_2);
x_4 = l_Std_Internal_Rat_mul(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Rat_div(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_nat_gcd(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_nat_div(x_4, x_8);
lean_dec(x_4);
x_12 = lean_nat_mul(x_11, x_7);
x_13 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_int_mul(x_14, x_3);
lean_dec(x_3);
lean_dec(x_14);
x_16 = lean_nat_to_int(x_11);
x_17 = lean_int_mul(x_16, x_6);
lean_dec(x_6);
lean_dec(x_16);
x_18 = lean_int_add(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
x_19 = lean_nat_abs(x_18);
x_20 = lean_nat_gcd(x_19, x_8);
lean_dec(x_8);
lean_dec(x_19);
x_21 = lean_nat_dec_eq(x_20, x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_20);
x_22 = lean_nat_to_int(x_20);
x_23 = lean_int_div(x_18, x_22);
lean_dec(x_22);
lean_dec(x_18);
x_24 = lean_nat_div(x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_23);
return x_2;
}
else
{
lean_dec(x_20);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
lean_inc(x_7);
x_25 = lean_nat_to_int(x_7);
x_26 = lean_int_mul(x_3, x_25);
lean_dec(x_25);
lean_dec(x_3);
lean_inc(x_4);
x_27 = lean_nat_to_int(x_4);
x_28 = lean_int_mul(x_6, x_27);
lean_dec(x_27);
lean_dec(x_6);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = lean_nat_mul(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_29);
return x_2;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_33 = lean_nat_gcd(x_4, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_36 = lean_nat_div(x_4, x_33);
lean_dec(x_4);
x_37 = lean_nat_mul(x_36, x_32);
x_38 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_39 = lean_nat_to_int(x_38);
x_40 = lean_int_mul(x_39, x_3);
lean_dec(x_3);
lean_dec(x_39);
x_41 = lean_nat_to_int(x_36);
x_42 = lean_int_mul(x_41, x_31);
lean_dec(x_31);
lean_dec(x_41);
x_43 = lean_int_add(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
x_44 = lean_nat_abs(x_43);
x_45 = lean_nat_gcd(x_44, x_33);
lean_dec(x_33);
lean_dec(x_44);
x_46 = lean_nat_dec_eq(x_45, x_34);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_45);
x_47 = lean_nat_to_int(x_45);
x_48 = lean_int_div(x_43, x_47);
lean_dec(x_47);
lean_dec(x_43);
x_49 = lean_nat_div(x_37, x_45);
lean_dec(x_45);
lean_dec(x_37);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_37);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_33);
lean_inc(x_32);
x_52 = lean_nat_to_int(x_32);
x_53 = lean_int_mul(x_3, x_52);
lean_dec(x_52);
lean_dec(x_3);
lean_inc(x_4);
x_54 = lean_nat_to_int(x_4);
x_55 = lean_int_mul(x_31, x_54);
lean_dec(x_54);
lean_dec(x_31);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = lean_nat_mul(x_4, x_32);
lean_dec(x_32);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_sub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_nat_gcd(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_11 = lean_nat_div(x_4, x_8);
x_12 = lean_nat_mul(x_11, x_7);
lean_dec(x_11);
x_13 = lean_nat_to_int(x_7);
lean_inc(x_8);
x_14 = lean_nat_to_int(x_8);
x_15 = lean_int_ediv(x_13, x_14);
lean_dec(x_13);
x_16 = lean_int_mul(x_15, x_3);
lean_dec(x_3);
lean_dec(x_15);
x_17 = lean_nat_to_int(x_4);
x_18 = lean_int_ediv(x_17, x_14);
lean_dec(x_14);
lean_dec(x_17);
x_19 = lean_int_mul(x_18, x_6);
lean_dec(x_6);
lean_dec(x_18);
x_20 = lean_int_sub(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_nat_abs(x_20);
x_22 = lean_nat_gcd(x_21, x_8);
lean_dec(x_8);
lean_dec(x_21);
x_23 = lean_nat_dec_eq(x_22, x_9);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_22);
x_24 = lean_nat_to_int(x_22);
x_25 = lean_int_div(x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
x_26 = lean_nat_div(x_12, x_22);
lean_dec(x_22);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_dec(x_22);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_20);
return x_2;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_inc(x_7);
x_27 = lean_nat_to_int(x_7);
x_28 = lean_int_mul(x_3, x_27);
lean_dec(x_27);
lean_dec(x_3);
lean_inc(x_4);
x_29 = lean_nat_to_int(x_4);
x_30 = lean_int_mul(x_6, x_29);
lean_dec(x_29);
lean_dec(x_6);
x_31 = lean_int_sub(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_32 = lean_nat_mul(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_nat_gcd(x_4, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_38 = lean_nat_div(x_4, x_35);
x_39 = lean_nat_mul(x_38, x_34);
lean_dec(x_38);
x_40 = lean_nat_to_int(x_34);
lean_inc(x_35);
x_41 = lean_nat_to_int(x_35);
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = lean_int_mul(x_42, x_3);
lean_dec(x_3);
lean_dec(x_42);
x_44 = lean_nat_to_int(x_4);
x_45 = lean_int_ediv(x_44, x_41);
lean_dec(x_41);
lean_dec(x_44);
x_46 = lean_int_mul(x_45, x_33);
lean_dec(x_33);
lean_dec(x_45);
x_47 = lean_int_sub(x_43, x_46);
lean_dec(x_46);
lean_dec(x_43);
x_48 = lean_nat_abs(x_47);
x_49 = lean_nat_gcd(x_48, x_35);
lean_dec(x_35);
lean_dec(x_48);
x_50 = lean_nat_dec_eq(x_49, x_36);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc(x_49);
x_51 = lean_nat_to_int(x_49);
x_52 = lean_int_div(x_47, x_51);
lean_dec(x_51);
lean_dec(x_47);
x_53 = lean_nat_div(x_39, x_49);
lean_dec(x_49);
lean_dec(x_39);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_39);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_35);
lean_inc(x_34);
x_56 = lean_nat_to_int(x_34);
x_57 = lean_int_mul(x_3, x_56);
lean_dec(x_56);
lean_dec(x_3);
lean_inc(x_4);
x_58 = lean_nat_to_int(x_4);
x_59 = lean_int_mul(x_33, x_58);
lean_dec(x_58);
lean_dec(x_33);
x_60 = lean_int_sub(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
x_61 = lean_nat_mul(x_4, x_34);
lean_dec(x_34);
lean_dec(x_4);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_neg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Rat_floor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_nat_to_int(x_3);
x_7 = lean_int_ediv(x_2, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_ceil(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_nat_to_int(x_3);
x_7 = l_Int_Linear_cdiv(x_2, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
static lean_object* _init_l_Std_Internal_Rat_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Rat_instDecidableLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Internal_Rat_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Rat_instDecidableLt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Rat_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Rat_instDecidableLe(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = l_Std_Internal_Rat_lt(x_2, x_1);
x_4 = l_instDecidableNot___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Rat_instDecidableLe(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Rat_instAdd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Rat_add), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Rat_instAdd___closed__0;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instSub___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Rat_sub), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instSub() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Rat_instSub___closed__0;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instNeg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Rat_neg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instNeg() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Rat_instNeg___closed__0;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instMul___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Rat_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_Rat_instMul() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_Rat_instMul___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDiv___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Rat_inv(x_2);
x_4 = l_Std_Internal_Rat_mul(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_Rat_instDiv() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Rat_instDiv___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instDiv___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Rat_instDiv___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instOfNat(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Std_Internal_Rat_instCoeInt___lam__0(lean_object* x_1) {
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
static lean_object* _init_l_Std_Internal_Rat_instCoeInt() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Rat_instCoeInt___lam__0), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Rat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_instInhabitedRat___closed__0 = _init_l_Std_Internal_instInhabitedRat___closed__0();
lean_mark_persistent(l_Std_Internal_instInhabitedRat___closed__0);
l_Std_Internal_instInhabitedRat___closed__1 = _init_l_Std_Internal_instInhabitedRat___closed__1();
lean_mark_persistent(l_Std_Internal_instInhabitedRat___closed__1);
l_Std_Internal_instInhabitedRat = _init_l_Std_Internal_instInhabitedRat();
lean_mark_persistent(l_Std_Internal_instInhabitedRat);
l_Std_Internal_instBEqRat___closed__0 = _init_l_Std_Internal_instBEqRat___closed__0();
lean_mark_persistent(l_Std_Internal_instBEqRat___closed__0);
l_Std_Internal_instBEqRat = _init_l_Std_Internal_instBEqRat();
lean_mark_persistent(l_Std_Internal_instBEqRat);
l_Std_Internal_instToStringRat___lam__0___closed__0 = _init_l_Std_Internal_instToStringRat___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_instToStringRat___lam__0___closed__0);
l_Std_Internal_instToStringRat___lam__0___closed__1 = _init_l_Std_Internal_instToStringRat___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_instToStringRat___lam__0___closed__1);
l_Std_Internal_instToStringRat = _init_l_Std_Internal_instToStringRat();
lean_mark_persistent(l_Std_Internal_instToStringRat);
l_Std_Internal_instReprRat___lam__0___closed__0 = _init_l_Std_Internal_instReprRat___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_instReprRat___lam__0___closed__0);
l_Std_Internal_instReprRat___lam__0___closed__1 = _init_l_Std_Internal_instReprRat___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_instReprRat___lam__0___closed__1);
l_Std_Internal_instReprRat = _init_l_Std_Internal_instReprRat();
lean_mark_persistent(l_Std_Internal_instReprRat);
l_Std_Internal_mkRat___closed__0 = _init_l_Std_Internal_mkRat___closed__0();
lean_mark_persistent(l_Std_Internal_mkRat___closed__0);
l_Std_Internal_Rat_instLT = _init_l_Std_Internal_Rat_instLT();
lean_mark_persistent(l_Std_Internal_Rat_instLT);
l_Std_Internal_Rat_instLE = _init_l_Std_Internal_Rat_instLE();
lean_mark_persistent(l_Std_Internal_Rat_instLE);
l_Std_Internal_Rat_instAdd___closed__0 = _init_l_Std_Internal_Rat_instAdd___closed__0();
lean_mark_persistent(l_Std_Internal_Rat_instAdd___closed__0);
l_Std_Internal_Rat_instAdd = _init_l_Std_Internal_Rat_instAdd();
lean_mark_persistent(l_Std_Internal_Rat_instAdd);
l_Std_Internal_Rat_instSub___closed__0 = _init_l_Std_Internal_Rat_instSub___closed__0();
lean_mark_persistent(l_Std_Internal_Rat_instSub___closed__0);
l_Std_Internal_Rat_instSub = _init_l_Std_Internal_Rat_instSub();
lean_mark_persistent(l_Std_Internal_Rat_instSub);
l_Std_Internal_Rat_instNeg___closed__0 = _init_l_Std_Internal_Rat_instNeg___closed__0();
lean_mark_persistent(l_Std_Internal_Rat_instNeg___closed__0);
l_Std_Internal_Rat_instNeg = _init_l_Std_Internal_Rat_instNeg();
lean_mark_persistent(l_Std_Internal_Rat_instNeg);
l_Std_Internal_Rat_instMul___closed__0 = _init_l_Std_Internal_Rat_instMul___closed__0();
lean_mark_persistent(l_Std_Internal_Rat_instMul___closed__0);
l_Std_Internal_Rat_instMul = _init_l_Std_Internal_Rat_instMul();
lean_mark_persistent(l_Std_Internal_Rat_instMul);
l_Std_Internal_Rat_instDiv = _init_l_Std_Internal_Rat_instDiv();
lean_mark_persistent(l_Std_Internal_Rat_instDiv);
l_Std_Internal_Rat_instCoeInt = _init_l_Std_Internal_Rat_instCoeInt();
lean_mark_persistent(l_Std_Internal_Rat_instCoeInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

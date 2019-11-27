// Lean compiler output
// Module: Init.Data.Int.Basic
// Imports: Init.Data.Nat.Basic Init.Data.List Init.Coe Init.Data.Repr Init.Data.ToString
#include "runtime/lean.h"
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
uint8_t l_String_isInt(lean_object*);
lean_object* l_Int_HasNeg;
lean_object* l_Int_natMod(lean_object*, lean_object*);
uint8_t l_String_isInt___closed__1;
lean_object* l_Int_repr___boxed(lean_object*);
lean_object* l_Int_HasOne;
lean_object* l_Int_repr___closed__1;
lean_object* l_String_isInt___boxed(lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int_HasMod___closed__1;
lean_object* l_String_toNat(lean_object*);
uint8_t l_Int_Int_DecidableEq(lean_object*, lean_object*);
lean_object* l_Int_negSucc___boxed(lean_object*);
lean_object* l_Int_HasRepr;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Int_HasZero;
lean_object* l_Int_HasAdd;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Int_HasSub___closed__1;
lean_object* l_Int_zero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_toInt___closed__1;
lean_object* l_Int_decLt___boxed(lean_object*, lean_object*);
lean_object* l_String_toInt___closed__2;
lean_object* l_Int_repr(lean_object*);
lean_object* l_Int_HasLessEq;
lean_object* l_Int_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* l_Int_mul___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_decLe___boxed(lean_object*, lean_object*);
lean_object* l_Int_div___boxed(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Int_zero___closed__1;
lean_object* l_Int_Int_DecidableEq___boxed(lean_object*, lean_object*);
uint8_t l_Substring_isNat(lean_object*);
lean_object* l_Int_HasMul___closed__1;
lean_object* l_Int_subNatNat(lean_object*, lean_object*);
lean_object* l_Int_toNat___boxed(lean_object*);
lean_object* l_Int_mod___boxed(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Int_HasSub;
uint8_t l_String_isNat(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Int_HasDiv;
lean_object* l_Int_negOfNat___boxed(lean_object*);
lean_object* l_Int_HasAdd___closed__1;
lean_object* l_Int_natMod___boxed(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_one___closed__1;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
extern lean_object* l_Substring_drop___closed__2;
lean_object* lean_int_neg_succ_of_nat(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_one;
lean_object* l_Int_HasCoe(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* l_Int_HasMul;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Int_HasLess;
lean_object* l_String_toInt___closed__3;
lean_object* l_Int_subNatNat___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_HasDiv___closed__1;
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Int_Basic_1__decNonneg___boxed(lean_object*);
lean_object* l_Int_HasToString;
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* l_String_toInt(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_HasRepr___closed__1;
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_natAbs___boxed(lean_object*);
lean_object* l_Int_neg___boxed(lean_object*);
lean_object* l_Int_HasMod;
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Int_HasNeg___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Substring_toNat(lean_object*);
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
lean_object* l_Int_HasCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l_Int_zero___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l_Int_zero() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_zero___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_one___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l_Int_one() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_one___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_HasZero() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_zero;
return x_1;
}
}
lean_object* _init_l_Int_HasOne() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_one;
return x_1;
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
x_7 = l_Int_zero;
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
lean_object* _init_l_Int_HasNeg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_neg___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasNeg() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasNeg___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_HasAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasAdd() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasAdd___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_HasMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mul___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasMul() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasMul___closed__1;
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
lean_object* _init_l_Int_HasSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_sub___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasSub() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasSub___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_HasLessEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Int_HasLess() {
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
uint8_t l_Int_Int_DecidableEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Int_Int_DecidableEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Int_Int_DecidableEq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Data_Int_Basic_1__decNonneg___boxed(lean_object* x_1) {
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
lean_object* _init_l_Int_repr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-");
return x_1;
}
}
lean_object* l_Int_repr(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_zero___closed__1;
x_3 = lean_int_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_abs(x_1);
x_5 = l_Nat_repr(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_nat_abs(x_1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_add(x_8, x_7);
lean_dec(x_8);
x_10 = l_Nat_repr(x_9);
x_11 = l_Int_repr___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_Int_repr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_repr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Int_HasRepr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_repr___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasRepr___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasRepr___closed__1;
return x_1;
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
lean_object* _init_l_Int_HasDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_div___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasDiv___closed__1;
return x_1;
}
}
lean_object* _init_l_Int_HasMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_mod___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Int_HasMod() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_HasMod___closed__1;
return x_1;
}
}
lean_object* l_Int_toNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Int_zero___closed__1;
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
lean_object* _init_l_String_toInt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Substring_drop___closed__2;
x_2 = l_Substring_toNat(x_1);
return x_2;
}
}
lean_object* _init_l_String_toInt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_toInt___closed__1;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l_String_toInt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_toInt___closed__2;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
lean_object* l_String_toInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_String_toNat(x_1);
lean_dec(x_1);
x_7 = lean_nat_to_int(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_le(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_8);
x_12 = l_Substring_toNat(x_11);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_neg(x_13);
lean_dec(x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_1);
x_15 = l_String_toInt___closed__3;
return x_15;
}
}
}
}
uint8_t _init_l_String_isInt___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Substring_drop___closed__2;
x_2 = l_Substring_isNat(x_1);
return x_2;
}
}
uint8_t l_String_isInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_get(x_1, x_2);
x_4 = 45;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_String_isNat(x_1);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_le(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_7);
x_11 = l_Substring_isNat(x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_String_isInt___closed__1;
return x_12;
}
}
}
}
lean_object* l_String_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isInt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
lean_object* initialize_Init_Data_List(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
lean_object* initialize_Init_Data_Repr(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Int_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Coe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_zero___closed__1 = _init_l_Int_zero___closed__1();
lean_mark_persistent(l_Int_zero___closed__1);
l_Int_zero = _init_l_Int_zero();
lean_mark_persistent(l_Int_zero);
l_Int_one___closed__1 = _init_l_Int_one___closed__1();
lean_mark_persistent(l_Int_one___closed__1);
l_Int_one = _init_l_Int_one();
lean_mark_persistent(l_Int_one);
l_Int_HasZero = _init_l_Int_HasZero();
lean_mark_persistent(l_Int_HasZero);
l_Int_HasOne = _init_l_Int_HasOne();
lean_mark_persistent(l_Int_HasOne);
l_Int_HasNeg___closed__1 = _init_l_Int_HasNeg___closed__1();
lean_mark_persistent(l_Int_HasNeg___closed__1);
l_Int_HasNeg = _init_l_Int_HasNeg();
lean_mark_persistent(l_Int_HasNeg);
l_Int_HasAdd___closed__1 = _init_l_Int_HasAdd___closed__1();
lean_mark_persistent(l_Int_HasAdd___closed__1);
l_Int_HasAdd = _init_l_Int_HasAdd();
lean_mark_persistent(l_Int_HasAdd);
l_Int_HasMul___closed__1 = _init_l_Int_HasMul___closed__1();
lean_mark_persistent(l_Int_HasMul___closed__1);
l_Int_HasMul = _init_l_Int_HasMul();
lean_mark_persistent(l_Int_HasMul);
l_Int_HasSub___closed__1 = _init_l_Int_HasSub___closed__1();
lean_mark_persistent(l_Int_HasSub___closed__1);
l_Int_HasSub = _init_l_Int_HasSub();
lean_mark_persistent(l_Int_HasSub);
l_Int_HasLessEq = _init_l_Int_HasLessEq();
lean_mark_persistent(l_Int_HasLessEq);
l_Int_HasLess = _init_l_Int_HasLess();
lean_mark_persistent(l_Int_HasLess);
l_Int_repr___closed__1 = _init_l_Int_repr___closed__1();
lean_mark_persistent(l_Int_repr___closed__1);
l_Int_HasRepr___closed__1 = _init_l_Int_HasRepr___closed__1();
lean_mark_persistent(l_Int_HasRepr___closed__1);
l_Int_HasRepr = _init_l_Int_HasRepr();
lean_mark_persistent(l_Int_HasRepr);
l_Int_HasToString = _init_l_Int_HasToString();
lean_mark_persistent(l_Int_HasToString);
l_Int_HasDiv___closed__1 = _init_l_Int_HasDiv___closed__1();
lean_mark_persistent(l_Int_HasDiv___closed__1);
l_Int_HasDiv = _init_l_Int_HasDiv();
lean_mark_persistent(l_Int_HasDiv);
l_Int_HasMod___closed__1 = _init_l_Int_HasMod___closed__1();
lean_mark_persistent(l_Int_HasMod___closed__1);
l_Int_HasMod = _init_l_Int_HasMod();
lean_mark_persistent(l_Int_HasMod);
l_String_toInt___closed__1 = _init_l_String_toInt___closed__1();
lean_mark_persistent(l_String_toInt___closed__1);
l_String_toInt___closed__2 = _init_l_String_toInt___closed__2();
lean_mark_persistent(l_String_toInt___closed__2);
l_String_toInt___closed__3 = _init_l_String_toInt___closed__3();
lean_mark_persistent(l_String_toInt___closed__3);
l_String_isInt___closed__1 = _init_l_String_isInt___closed__1();
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
